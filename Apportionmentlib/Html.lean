/-
Copyright (c) 2026 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
module

public meta import Apportionmentlib.Basic
public import Apportionmentlib.Basic
public import ProofWidgets.Component.HtmlDisplay

/-!
# HTML rendering

In this file, we define a `HtmlEval` instance so that elections can be rendered as a table using the
`#html` command from ProofWidgets.
-/

public meta section

open ProofWidgets
open Lean (Json)

namespace Apportionmentlib

/-- Renders an election as a table of the votes and quotas of all parties. -/
def Election.toHtml {n : ℕ} (e : Election n) : Html :=
  let indices := List.range n
  let votesList := e.votes.toList
  let houseSize := e.houseSize
  let total := votesList.sum
  let thStyle := Json.mkObj [
    ("border", Json.str "1px solid"),
    ("padding", Json.str "6px"),
    ("textAlign", Json.str "center")
  ]
  let tdStyle := Json.mkObj [
    ("border", Json.str "1px solid"),
    ("padding", Json.str "6px"),
    ("textAlign", Json.str "center"),
    ("fontFamily", Json.str "monospace")
  ]
  let tableStyle := Json.mkObj [
    ("borderCollapse", Json.str "collapse"),
  ]
  let th (s : String) := Html.element "th" #[("style", thStyle)] #[Html.text s]
  let td (s : String) := Html.element "td" #[("style", tdStyle)] #[Html.text s]
  let row1 := Html.element "tr" #[] <|
    ([th "id"] ++ indices.map (fun i => th (toString i)) ++ [th "Σ"]).toArray
  let row2 := Html.element "tr" #[] <|
    ([th "votes"] ++ votesList.map (fun v => td (toString v)) ++ [td s!"{total}"]).toArray
  let row3 := Html.element "tr" #[] <|
    ([th "quota"] ++ (List.finRange n).map (fun i => td (formatRat4 (e.quota i))) ++
     [td s!"{houseSize.val}"]).toArray
  Html.element "table" #[("style", tableStyle)] #[Html.element "tbody" #[] #[row1, row2, row3]]

/-- This instance enables rendering of elections using the `#html` command. For example,
```lean
#html election![8; [66, 67, 245, 622]]
```
-/
instance {n : ℕ} : HtmlEval (Election n) where
  eval e := pure e.toHtml

end Apportionmentlib
