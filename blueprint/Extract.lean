import GraphChoices
import Lean.Util.FoldConsts

open Lean Elab Command

elab "#export_graph_choices_dependencies" : command => do
  let env ← getEnv
  let namesText ← IO.FS.readFile "blueprint/source_names.txt"
  let targets := namesText.splitOn "\n"
  let rows ← liftTermElabM do
    let mut rows : Array Json := #[]
    for (n, c) in env.constants.toList do
      let name := n.toString
      if name.startsWith "GraphChoices." || name.startsWith "_private.GraphChoices." then
        let used := c.getUsedConstantsAsSet.toArray.map fun n => Json.str n.toString
        let kind := match c with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque"
          | _ => "other"
        let statement ← if targets.contains name then
          -- The upper theorem is stated through a named proposition. Show
          -- its unfolded specification so the reader sees the quantifiers.
          let type ← if name == "GraphChoices.mainTheorem" then Meta.whnf c.type else pure c.type
          pure (← Meta.ppExpr type).pretty
          else pure ""
        rows := rows.push <| Json.mkObj [
          ("name", .str name), ("kind", .str kind),
          ("used", .arr used), ("statement", .str statement)]
    pure rows
  IO.FS.writeFile "blueprint/compiled_dependencies.json" (Json.arr rows).pretty
  logInfo m!"Exported {rows.size} project declarations from the compiled Lean environment."

#export_graph_choices_dependencies
