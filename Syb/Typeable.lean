import Lean

open Lean Elab Command Meta

inductive TypeRep where
| typeRep : String → TypeRep
| app : TypeRep → TypeRep → TypeRep
| appTerm : TypeRep → String → TypeRep → TypeRep  -- Now includes type signature
deriving BEq

def TypeRep.stringify : TypeRep → String
| .typeRep r => r
| .app f a => s!"({f.stringify} {a.stringify})"
| .appTerm f t ty => s!"({f.stringify} {t}:{ty.stringify})"

instance : ToString TypeRep where
  toString := TypeRep.stringify

class Typeable (α : Type u) where
  typeOf : α → TypeRep
  typeRep : TypeRep

-- Helper to check if an expression is a type (Sort u)
partial def isTypeParam (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isSort then
    return true
  else if type.isForall then
    isTypeParam type.bindingBody!
  else
    return false

def deriveTypeable : DerivingHandler := fun declNames => do
  for declName in declNames do
    let env ← getEnv
    let some declInfo := env.find? declName
      | throwError "Unknown declaration {declName}"
    
    let uniqueStr ← liftTermElabM do
      let freshName ← mkFreshId
      return freshName.toString
    
    let (numParams, params) := match declInfo with
      | .inductInfo val => (val.numParams, val.type)
      | .ctorInfo val => (val.numParams, val.type)
      | _ => (0, .const ``Unit [])
    
    if numParams > 0 then
      -- Analyze parameter types
      let mut paramInfos : Array (Name × Bool × Expr) := #[] -- (name, isType, type)
      
      let mut expr := params
      for _ in [:numParams] do
        expr ← liftTermElabM do whnf expr
        if expr.isForall then
          let n := expr.bindingName!
          let ty := expr.bindingDomain!
          let isType ← liftTermElabM do isTypeParam ty
          paramInfos := paramInfos.push (n, isType, ty)
          expr := expr.bindingBody!
        else
          break
      
      -- Build the binders
      let mut allBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
      let mut instBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
      
      for i in [:numParams] do
        let (origName, isType, paramType) := paramInfos[i]!
        let paramName := if origName.isAnonymous then 
          Name.mkSimple s!"A{i}" 
        else 
          origName
        
        if isType then
          allBinders := allBinders.push (← `(bracketedBinder| {$(mkIdent paramName) : Type _}))
          let instName := Name.mkSimple s!"inst{i}"
          instBinders := instBinders.push (← `(bracketedBinder| [$(mkIdent instName) : Typeable $(mkIdent paramName)]))
        else
          -- For term parameters, delab the type expression
          let typeStx ← liftTermElabM do
            PrettyPrinter.delab paramType
          allBinders := allBinders.push (← `(bracketedBinder| ($(mkIdent paramName) : $typeStx)))
          -- Need both ToString and Typeable for the type
          let instNameToString := Name.mkSimple s!"instToString{i}"
          instBinders := instBinders.push (← `(bracketedBinder| [$(mkIdent instNameToString) : ToString $typeStx]))
          let instNameTypeable := Name.mkSimple s!"instTypeable{i}"
          instBinders := instBinders.push (← `(bracketedBinder| [$(mkIdent instNameTypeable) : Typeable $typeStx]))
      
      allBinders := allBinders ++ instBinders
      
      -- Build the type application
      let mut typeApp : Term ← `($(mkIdent declName))
      for i in [:numParams] do
        let (origName, _, _) := paramInfos[i]!
        let paramName := if origName.isAnonymous then 
          Name.mkSimple s!"A{i}" 
        else 
          origName
        typeApp ← `($typeApp $(mkIdent paramName))
      
      -- Build the TypeRep expression
      let baseRep := quote (declName.toString ++ uniqueStr)
      let mut repExpr : Term ← `(.typeRep $baseRep)
      for i in [:numParams] do
        let (origName, isType, paramType) := paramInfos[i]!
        let paramName := if origName.isAnonymous then 
          Name.mkSimple s!"A{i}" 
        else 
          origName
        
        if isType then
          repExpr ← `(.app $repExpr (Typeable.typeRep (α := $(mkIdent paramName))))
        else
          -- Include the type signature in the appTerm
          let typeStx ← liftTermElabM do
            PrettyPrinter.delab paramType
          repExpr ← `(.appTerm $repExpr (toString $(mkIdent paramName)) (Typeable.typeRep (α := $typeStx)))
      
      let cmd ← `(command|
        instance $[$allBinders]* : Typeable $typeApp where
          typeOf _ := $repExpr
          typeRep := $repExpr
      )
      
      elabCommand cmd
    else
      let cmd ← `(command|
        instance : Typeable $(mkIdent declName) where
          typeOf _ := .typeRep $(quote $ declName.toString ++ uniqueStr)
          typeRep := .typeRep $(quote $ declName.toString ++ uniqueStr)
      )
      
      elabCommand cmd
  
  return true

initialize
  registerDerivingHandler ``Typeable deriveTypeable
