import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3588

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def pad4 (y : Fin 8 → Bool) : Fin 9 → Bool :=
  ![y 0, y 1, y 2, y 3, Bool.false, y 4, y 5, y 6, y 7]

private def makeX6 (x5 : Fin 9 → Bool) : List Bool :=
  List.ofFn x5 ++ [x5 (0 : Fin 9) || x5 (4 : Fin 9)]

private def makeInp (x5 : Fin 9 → Bool) (x2 : Fin 11) : List Bool :=
  let x6 := makeX6 x5
  x6 ++ [x6.getD (↑x2) Bool.false]

private def env10 : List (Sum Bool Nat) :=
  [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
   Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 0]

private def env0 (x2 : Fin 11) : List (Sum Bool Nat) :=
  env10 ++ [env10.getD (↑x2) (Sum.inl false)]

private def evalSym (w : List Bool) : Sum Bool Nat → Bool
  | Sum.inl b => b
  | Sum.inr idx => w.getD idx false

private def gateEval (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def runGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gateEval w g]) x

private def isFanInTwoGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def stepGate (st : List (Sum Bool Nat) × List Gate) (g : Gate) :
    List (Sum Bool Nat) × List Gate :=
  let env := st.1
  let gs := st.2
  let lk (i : Nat) : Sum Bool Nat := env.getD i (Sum.inl false)
  let next := 8 + gs.length
  match g.op, g.inputs with
  | GateOp.and, [] => (env ++ [Sum.inl true], gs)
  | GateOp.and, [a] => (env ++ [lk a], gs)
  | GateOp.and, [a, b] =>
    match lk a, lk b with
    | Sum.inl false, _ => (env ++ [Sum.inl false], gs)
    | _, Sum.inl false => (env ++ [Sum.inl false], gs)
    | Sum.inl true, sb => (env ++ [sb], gs)
    | sa, Sum.inl true => (env ++ [sa], gs)
    | Sum.inr ia, Sum.inr ib => (env ++ [Sum.inr next], gs ++ [⟨GateOp.and, [ia, ib]⟩])
  | GateOp.or, [] => (env ++ [Sum.inl false], gs)
  | GateOp.or, [a] => (env ++ [lk a], gs)
  | GateOp.or, [a, b] =>
    match lk a, lk b with
    | Sum.inl true, _ => (env ++ [Sum.inl true], gs)
    | _, Sum.inl true => (env ++ [Sum.inl true], gs)
    | Sum.inl false, sb => (env ++ [sb], gs)
    | sa, Sum.inl false => (env ++ [sa], gs)
    | Sum.inr ia, Sum.inr ib => (env ++ [Sum.inr next], gs ++ [⟨GateOp.or, [ia, ib]⟩])
  | GateOp.not, [] => (env ++ [Sum.inl true], gs)
  | GateOp.not, a :: _ =>
    match lk a with
    | Sum.inl b => (env ++ [Sum.inl (!b)], gs)
    | Sum.inr ia => (env ++ [Sum.inr next], gs ++ [⟨GateOp.not, [ia]⟩])
  | _, _ => (env ++ [Sum.inl false], gs)

private lemma getD_append_singleton {α : Type*} (l : List α) (v d : α) (i : Nat) :
    (l ++ [v]).getD i d =
      if i < l.length then l.getD i d else if i = l.length then v else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : i = l.length
    · subst h2
      simp
    · rw [if_neg h2]
      have h3 : l.length + 1 ≤ i := by omega
      have h4 : (l ++ [v]).length ≤ i := by simpa using h3
      rw [List.getElem?_eq_none h4]
      rfl

private lemma runGates_length (gs : List Gate) (x : List Bool) :
    (runGates gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [runGates]
  | cons g rest ih =>
    simp only [runGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

private lemma runGates_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    runGates (gs ++ [g]) x = runGates gs x ++ [gateEval (runGates gs x) g] := by
  simp [runGates, List.foldl_append]

private lemma evalSym_append_of_lt (w : List Bool) (v : Bool) (s : Sum Bool Nat)
    (hs : ∀ idx, s = Sum.inr idx → idx < w.length) :
    evalSym (w ++ [v]) s = evalSym w s := by
  cases s with
  | inl b => rfl
  | inr idx =>
    simp only [evalSym, getD_append_singleton]
    rw [if_pos (hs idx rfl)]

private lemma makeX6_length (x5 : Fin 9 → Bool) : (makeX6 x5).length = 10 := by
  simp [makeX6]

private lemma makeInp_length (x5 : Fin 9 → Bool) (x2 : Fin 11) :
    (makeInp x5 x2).length = 11 := by
  simp [makeInp, makeX6]

private lemma env10_getD_bound (i idx : Nat) (h : env10.getD i (Sum.inl false) = Sum.inr idx) :
    idx < 8 := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [env10] at h <;> omega

private lemma env0_length (x2 : Fin 11) : (env0 x2).length = 11 := by
  simp [env0, env10]

private lemma env0_getD_bound (x2 : Fin 11) (i idx : Nat)
    (h : (env0 x2).getD i (Sum.inl false) = Sum.inr idx) : idx < 8 := by
  rw [env0, getD_append_singleton] at h
  by_cases h1 : i < env10.length
  · rw [if_pos h1] at h
    exact env10_getD_bound i idx h
  · rw [if_neg h1] at h
    by_cases h2 : i = env10.length
    · rw [if_pos h2] at h
      exact env10_getD_bound x2.val idx h
    · rw [if_neg h2] at h
      cases h

private lemma makeX6_pad4_getD (y : Fin 8 → Bool) (i : Nat) :
    (makeX6 (pad4 y)).getD i false = evalSym (List.ofFn y) (env10.getD i (Sum.inl false)) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · simp [makeX6, pad4, env10, evalSym, List.getD_eq_getElem?_getD]
  · have h1 : (makeX6 (pad4 y)).length ≤ i + 10 := by simp [makeX6]
    have h2 : env10.length ≤ i + 10 := by simp [env10]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2, evalSym]

private lemma makeInp_pad4_getD (y : Fin 8 → Bool) (x2 : Fin 11) (i : Nat) :
    (makeInp (pad4 y) x2).getD i false =
      evalSym (List.ofFn y) ((env0 x2).getD i (Sum.inl false)) := by
  rw [makeInp, env0, getD_append_singleton, getD_append_singleton]
  have hlen : (makeX6 (pad4 y)).length = env10.length := by simp [makeX6, env10]
  rw [hlen]
  by_cases h1 : i < env10.length
  · rw [if_pos h1, if_pos h1]
    exact makeX6_pad4_getD y i
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i = env10.length
    · rw [if_pos h2, if_pos h2]
      exact makeX6_pad4_getD y x2.val
    · rw [if_neg h2, if_neg h2]
      rfl

private lemma makeX6_agree_of_isRight (x6 : Fin 9 → Bool) (h0 : x6 (0 : Fin 9) = true) (i : Nat)
    (hr : (env10.getD i (Sum.inl false)).isRight = true) :
    (makeX6 x6).getD i false = (makeX6 (Function.update x6 (4 : Fin 9) true)).getD i false := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [env10] at hr
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [makeX6, List.getD_eq_getElem?_getD]
  · simp [makeX6, List.getD_eq_getElem?_getD, h0]
  · have h2 : env10.length ≤ i + 10 := by simp [env10]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h2] at hr

private lemma makeInp_agree_of_isRight (x6 : Fin 9 → Bool) (h0 : x6 (0 : Fin 9) = true)
    (x2 : Fin 11) (i : Nat)
    (hr : ((env0 x2).getD i (Sum.inl false)).isRight = true) :
    (makeInp x6 x2).getD i false =
      (makeInp (Function.update x6 (4 : Fin 9) true) x2).getD i false := by
  rw [makeInp, makeInp, getD_append_singleton, getD_append_singleton]
  rw [env0, getD_append_singleton] at hr
  have hl1 : (makeX6 x6).length = env10.length := by simp [makeX6, env10]
  have hl2 : (makeX6 (Function.update x6 (4 : Fin 9) true)).length = env10.length := by
    simp [makeX6, env10]
  rw [hl1, hl2]
  by_cases h1 : i < env10.length
  · rw [if_pos h1, if_pos h1]
    rw [if_pos h1] at hr
    exact makeX6_agree_of_isRight x6 h0 i hr
  · rw [if_neg h1, if_neg h1]
    rw [if_neg h1] at hr
    by_cases h2 : i = env10.length
    · rw [if_pos h2, if_pos h2]
      rw [if_pos h2] at hr
      exact makeX6_agree_of_isRight x6 h0 x2.val hr
    · rw [if_neg h2] at hr
      simp at hr

private lemma gateEval_and_nil (w : List Bool) : gateEval w ⟨GateOp.and, []⟩ = true := rfl

private lemma gateEval_and_one (w : List Bool) (a : Nat) :
    gateEval w ⟨GateOp.and, [a]⟩ = w.getD a false := by
  simp only [gateEval, GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]

private lemma gateEval_and_two (w : List Bool) (a b : Nat) :
    gateEval w ⟨GateOp.and, [a, b]⟩ = (w.getD a false && w.getD b false) := by
  simp only [gateEval, GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]

private lemma gateEval_or_nil (w : List Bool) : gateEval w ⟨GateOp.or, []⟩ = false := rfl

private lemma gateEval_or_one (w : List Bool) (a : Nat) :
    gateEval w ⟨GateOp.or, [a]⟩ = w.getD a false := by
  simp only [gateEval, GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]

private lemma gateEval_or_two (w : List Bool) (a b : Nat) :
    gateEval w ⟨GateOp.or, [a, b]⟩ = (w.getD a false || w.getD b false) := by
  simp only [gateEval, GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]

private lemma gateEval_not_nil (w : List Bool) : gateEval w ⟨GateOp.not, []⟩ = true := rfl

private lemma gateEval_not_cons (w : List Bool) (a : Nat) (rest : List Nat) :
    gateEval w ⟨GateOp.not, a :: rest⟩ = !(w.getD a false) := rfl

private lemma stepGate_inv
    (env : List (Sum Bool Nat)) (gs : List Gate) (g : Gate)
    (hg : isFanInTwoGate g)
    (hfan : ∀ g' ∈ gs, isFanInTwoGate g')
    (hbound : ∀ i idx, env.getD i (Sum.inl false) = Sum.inr idx → idx < 8 + gs.length)
    (w_old : (Fin 8 → Bool) → List Bool)
    (hlen : ∀ y, (w_old y).length = env.length)
    (hsem : ∀ y i, (w_old y).getD i false =
      evalSym (runGates gs (List.ofFn y)) (env.getD i (Sum.inl false)))
    (w1 w2 : List Bool)
    (hl1 : w1.length = env.length) (hl2 : w2.length = env.length) :
    let st' := stepGate (env, gs) g
    st'.1.length = env.length + 1 ∧
    st'.2.length ≤ gs.length + 1 ∧
    (∀ g' ∈ st'.2, isFanInTwoGate g') ∧
    (∀ i idx, st'.1.getD i (Sum.inl false) = Sum.inr idx → idx < 8 + st'.2.length) ∧
    (∀ y, (w_old y ++ [gateEval (w_old y) g]).length = st'.1.length) ∧
    (∀ y i, (w_old y ++ [gateEval (w_old y) g]).getD i false =
      evalSym (runGates st'.2 (List.ofFn y)) (st'.1.getD i (Sum.inl false))) ∧
    ((∀ i, (env.getD i (Sum.inl false)).isRight = true → w1.getD i false = w2.getD i false) →
      st'.2.length = gs.length + 1 →
      ∀ i, (st'.1.getD i (Sum.inl false)).isRight = true →
        (w1 ++ [gateEval w1 g]).getD i false = (w2 ++ [gateEval w2 g]).getD i false) := by
  have hkeep : ∀ (s : Sum Bool Nat),
      (∀ idx, s = Sum.inr idx → idx < 8 + gs.length) →
      (∀ y, gateEval (w_old y) g = evalSym (runGates gs (List.ofFn y)) s) →
      (env ++ [s]).length = env.length + 1 ∧
      gs.length ≤ gs.length + 1 ∧
      (∀ g' ∈ gs, isFanInTwoGate g') ∧
      (∀ i idx, (env ++ [s]).getD i (Sum.inl false) = Sum.inr idx → idx < 8 + gs.length) ∧
      (∀ y, (w_old y ++ [gateEval (w_old y) g]).length = (env ++ [s]).length) ∧
      (∀ y i, (w_old y ++ [gateEval (w_old y) g]).getD i false =
        evalSym (runGates gs (List.ofFn y)) ((env ++ [s]).getD i (Sum.inl false))) ∧
      ((∀ i, (env.getD i (Sum.inl false)).isRight = true → w1.getD i false = w2.getD i false) →
        gs.length = gs.length + 1 →
        ∀ i, ((env ++ [s]).getD i (Sum.inl false)).isRight = true →
          (w1 ++ [gateEval w1 g]).getD i false = (w2 ++ [gateEval w2 g]).getD i false) := by
    intro s hs_lt hs_ev
    refine ⟨by simp, by omega, hfan, ?_, ?_, ?_, ?_⟩
    · intro i idx hi
      rw [getD_append_singleton] at hi
      by_cases h1 : i < env.length
      · rw [if_pos h1] at hi
        exact hbound i idx hi
      · rw [if_neg h1] at hi
        by_cases h2 : i = env.length
        · rw [if_pos h2] at hi
          exact hs_lt idx hi
        · rw [if_neg h2] at hi
          cases hi
    · intro y
      simp [hlen y]
    · intro y i
      rw [getD_append_singleton, getD_append_singleton, hlen y]
      by_cases h1 : i < env.length
      · rw [if_pos h1, if_pos h1]
        exact hsem y i
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : i = env.length
        · rw [if_pos h2, if_pos h2]
          exact hs_ev y
        · rw [if_neg h2, if_neg h2]
          rfl
    · intro _ hcontra
      omega
  have hadd : ∀ (gnew : Gate),
      isFanInTwoGate gnew →
      (∀ y, gateEval (w_old y) g = gateEval (runGates gs (List.ofFn y)) gnew) →
      ((∀ i, (env.getD i (Sum.inl false)).isRight = true → w1.getD i false = w2.getD i false) →
        gateEval w1 g = gateEval w2 g) →
      (env ++ [Sum.inr (8 + gs.length)]).length = env.length + 1 ∧
      (gs ++ [gnew]).length ≤ gs.length + 1 ∧
      (∀ g' ∈ gs ++ [gnew], isFanInTwoGate g') ∧
      (∀ i idx, (env ++ [Sum.inr (8 + gs.length)]).getD i (Sum.inl false) = Sum.inr idx →
        idx < 8 + (gs ++ [gnew]).length) ∧
      (∀ y, (w_old y ++ [gateEval (w_old y) g]).length = (env ++ [Sum.inr (8 + gs.length)]).length) ∧
      (∀ y i, (w_old y ++ [gateEval (w_old y) g]).getD i false =
        evalSym (runGates (gs ++ [gnew]) (List.ofFn y))
          ((env ++ [Sum.inr (8 + gs.length)]).getD i (Sum.inl false))) ∧
      ((∀ i, (env.getD i (Sum.inl false)).isRight = true → w1.getD i false = w2.getD i false) →
        (gs ++ [gnew]).length = gs.length + 1 →
        ∀ i, ((env ++ [Sum.inr (8 + gs.length)]).getD i (Sum.inl false)).isRight = true →
          (w1 ++ [gateEval w1 g]).getD i false = (w2 ++ [gateEval w2 g]).getD i false) := by
    intro gnew hgnew hev hag
    refine ⟨by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      rw [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact hfan g' hg'
      · exact hgnew
    · intro i idx hi
      rw [getD_append_singleton] at hi
      by_cases h1 : i < env.length
      · rw [if_pos h1] at hi
        have := hbound i idx hi
        simp
        omega
      · rw [if_neg h1] at hi
        by_cases h2 : i = env.length
        · rw [if_pos h2] at hi
          cases hi
          simp
        · rw [if_neg h2] at hi
          cases hi
    · intro y
      simp [hlen y]
    · intro y i
      rw [runGates_append_singleton]
      rw [getD_append_singleton, getD_append_singleton, hlen y]
      have hlen_new : (runGates gs (List.ofFn y)).length = 8 + gs.length := by
        rw [runGates_length, List.length_ofFn]
      by_cases h1 : i < env.length
      · rw [if_pos h1, if_pos h1]
        rw [evalSym_append_of_lt]
        · exact hsem y i
        · intro idx hidx
          rw [hlen_new]
          exact hbound i idx hidx
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : i = env.length
        · rw [if_pos h2, if_pos h2]
          simp only [evalSym, getD_append_singleton, hlen_new, lt_irrefl, ↓reduceIte]
          exact hev y
        · rw [if_neg h2, if_neg h2]
          rfl
    · intro hagree _ i hr
      rw [getD_append_singleton, getD_append_singleton, hl1, hl2]
      rw [getD_append_singleton] at hr
      by_cases h1 : i < env.length
      · rw [if_pos h1, if_pos h1]
        rw [if_pos h1] at hr
        exact hagree i hr
      · rw [if_neg h1, if_neg h1]
        rw [if_neg h1] at hr
        by_cases h2 : i = env.length
        · rw [if_pos h2, if_pos h2]
          exact hag hagree
        · rw [if_neg h2] at hr
          simp at hr
  rcases hg with ⟨hop, hlen_in⟩
  rcases g with ⟨op, inputs⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact hkeep (Sum.inl true) (by intro idx h; cases h) (by intro y; rfl)
    · exact hkeep (env.getD a (Sum.inl false)) (hbound a)
        (by intro y; rw [gateEval_and_one, hsem y a])
    · dsimp only [stepGate]
      cases ha : env.getD a (Sum.inl false) with
      | inl ba =>
        cases ba with
        | false =>
          exact hkeep (Sum.inl false) (by intro idx h; cases h)
            (by intro y; rw [gateEval_and_two, hsem y a, ha]; rfl)
        | true =>
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            cases bb with
            | false =>
              exact hkeep (Sum.inl false) (by intro idx h; cases h)
                (by intro y; rw [gateEval_and_two, hsem y b, hb]; simp [evalSym])
            | true =>
              exact hkeep (Sum.inl true) (by intro idx h; cases h)
                (by intro y; rw [gateEval_and_two, hsem y a, hsem y b, ha, hb]; rfl)
          | inr ib =>
            exact hkeep (Sum.inr ib) (by intro idx h; cases h; exact hbound b ib hb)
              (by intro y; rw [gateEval_and_two, hsem y a, hsem y b, ha, hb]; simp only [evalSym, Bool.true_and])
      | inr ia =>
        cases hb : env.getD b (Sum.inl false) with
        | inl bb =>
          cases bb with
          | false =>
            exact hkeep (Sum.inl false) (by intro idx h; cases h)
              (by intro y; rw [gateEval_and_two, hsem y b, hb]; simp [evalSym])
          | true =>
            exact hkeep (Sum.inr ia) (by intro idx h; cases h; exact hbound a ia ha)
              (by intro y; rw [gateEval_and_two, hsem y a, hsem y b, ha, hb]; simp only [evalSym, Bool.and_true])
        | inr ib =>
          exact hadd ⟨GateOp.and, [ia, ib]⟩
            ⟨by simp, by simp⟩
            (by intro y; rw [gateEval_and_two, gateEval_and_two, hsem y a, hsem y b, ha, hb]; rfl)
            (by
              intro hagree
              rw [gateEval_and_two, gateEval_and_two,
                hagree a (by rw [ha]; rfl), hagree b (by rw [hb]; rfl)])
    · simp at hlen_in
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact hkeep (Sum.inl false) (by intro idx h; cases h) (by intro y; rfl)
    · exact hkeep (env.getD a (Sum.inl false)) (hbound a)
        (by intro y; rw [gateEval_or_one, hsem y a])
    · dsimp only [stepGate]
      cases ha : env.getD a (Sum.inl false) with
      | inl ba =>
        cases ba with
        | true =>
          exact hkeep (Sum.inl true) (by intro idx h; cases h)
            (by intro y; rw [gateEval_or_two, hsem y a, ha]; rfl)
        | false =>
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            cases bb with
            | true =>
              exact hkeep (Sum.inl true) (by intro idx h; cases h)
                (by intro y; rw [gateEval_or_two, hsem y b, hb]; simp [evalSym])
            | false =>
              exact hkeep (Sum.inl false) (by intro idx h; cases h)
                (by intro y; rw [gateEval_or_two, hsem y a, hsem y b, ha, hb]; rfl)
          | inr ib =>
            exact hkeep (Sum.inr ib) (by intro idx h; cases h; exact hbound b ib hb)
              (by intro y; rw [gateEval_or_two, hsem y a, hsem y b, ha, hb]; simp only [evalSym, Bool.false_or])
      | inr ia =>
        cases hb : env.getD b (Sum.inl false) with
        | inl bb =>
          cases bb with
          | true =>
            exact hkeep (Sum.inl true) (by intro idx h; cases h)
              (by intro y; rw [gateEval_or_two, hsem y b, hb]; simp [evalSym])
          | false =>
            exact hkeep (Sum.inr ia) (by intro idx h; cases h; exact hbound a ia ha)
              (by intro y; rw [gateEval_or_two, hsem y a, hsem y b, ha, hb]; simp only [evalSym, Bool.or_false])
        | inr ib =>
          exact hadd ⟨GateOp.or, [ia, ib]⟩
            ⟨by simp, by simp⟩
            (by intro y; rw [gateEval_or_two, gateEval_or_two, hsem y a, hsem y b, ha, hb]; rfl)
            (by
              intro hagree
              rw [gateEval_or_two, gateEval_or_two,
                hagree a (by rw [ha]; rfl), hagree b (by rw [hb]; rfl)])
    · simp at hlen_in
  · rcases inputs with _ | ⟨a, rest⟩
    · exact hkeep (Sum.inl true) (by intro idx h; cases h) (by intro y; rfl)
    · dsimp only [stepGate]
      cases ha : env.getD a (Sum.inl false) with
      | inl ba =>
        exact hkeep (Sum.inl (!ba)) (by intro idx h; cases h)
          (by intro y; rw [gateEval_not_cons, hsem y a, ha]; rfl)
      | inr ia =>
        exact hadd ⟨GateOp.not, [ia]⟩
          ⟨by simp, by simp⟩
          (by intro y; rw [gateEval_not_cons, gateEval_not_cons, hsem y a, ha]; rfl)
          (by
            intro hagree
            rw [gateEval_not_cons, gateEval_not_cons, hagree a (by rw [ha]; rfl)])

private lemma fold_stepGate_inv
    (gates : List Gate)
    (hfan_gates : ∀ g ∈ gates, isFanInTwoGate g)
    (env : List (Sum Bool Nat)) (gs : List Gate)
    (hfan : ∀ g' ∈ gs, isFanInTwoGate g')
    (hbound : ∀ i idx, env.getD i (Sum.inl false) = Sum.inr idx → idx < 8 + gs.length)
    (w_old : (Fin 8 → Bool) → List Bool)
    (hlen : ∀ y, (w_old y).length = env.length)
    (hsem : ∀ y i, (w_old y).getD i false =
      evalSym (runGates gs (List.ofFn y)) (env.getD i (Sum.inl false)))
    (w1 w2 : List Bool)
    (hl1 : w1.length = env.length) (hl2 : w2.length = env.length)
    (hagree : ∀ i, (env.getD i (Sum.inl false)).isRight = true → w1.getD i false = w2.getD i false) :
    let stF := gates.foldl stepGate (env, gs)
    stF.2.length ≤ gs.length + gates.length ∧
    (∀ g' ∈ stF.2, isFanInTwoGate g') ∧
    (∀ y i, (runGates gates (w_old y)).getD i false =
      evalSym (runGates stF.2 (List.ofFn y)) (stF.1.getD i (Sum.inl false))) ∧
    (stF.2.length = gs.length + gates.length →
      ∀ i, (stF.1.getD i (Sum.inl false)).isRight = true →
        (runGates gates w1).getD i false = (runGates gates w2).getD i false) := by
  induction gates generalizing env gs w_old w1 w2 with
  | nil =>
    refine ⟨by simp, hfan, ?_, ?_⟩
    · intro y i
      simpa [runGates] using hsem y i
    · intro _ i hr
      simpa [runGates] using hagree i hr
  | cons g rest ih =>
    have hg : isFanInTwoGate g := hfan_gates g (by simp)
    have hrest : ∀ g' ∈ rest, isFanInTwoGate g' := fun g' hg' => hfan_gates g' (by simp [hg'])
    have hstep := stepGate_inv env gs g hg hfan hbound w_old hlen hsem w1 w2 hl1 hl2
    rcases hstep with ⟨hlen_env', hlen_gs', hfan', hbound', hlen_w', hsem', hagree'⟩
    simp only [List.foldl_cons, runGates]
    set st1 := stepGate (env, gs) g
    have hstep_len_w1 : (w1 ++ [gateEval w1 g]).length = st1.1.length := by simp [hl1, hlen_env']
    have hstep_len_w2 : (w2 ++ [gateEval w2 g]).length = st1.1.length := by simp [hl2, hlen_env']
    have hsub := ih hrest st1.1 st1.2 hfan' hbound'
      (fun y => w_old y ++ [gateEval (w_old y) g]) hlen_w' hsem'
      (w1 ++ [gateEval w1 g]) (w2 ++ [gateEval w2 g]) hstep_len_w1 hstep_len_w2
    have hmain_noagree :
        (rest.foldl stepGate st1).2.length ≤ st1.2.length + rest.length ∧
        (∀ g' ∈ (rest.foldl stepGate st1).2, isFanInTwoGate g') ∧
        (∀ y i, (runGates rest (w_old y ++ [gateEval (w_old y) g])).getD i false =
          evalSym (runGates (rest.foldl stepGate st1).2 (List.ofFn y))
            ((rest.foldl stepGate st1).1.getD i (Sum.inl false))) := by
      have hdummy := ih hrest st1.1 st1.2 hfan' hbound'
        (fun y => w_old y ++ [gateEval (w_old y) g]) hlen_w' hsem'
        (w1 ++ [gateEval w1 g]) (w1 ++ [gateEval w1 g]) hstep_len_w1 hstep_len_w1
        (by intro _ _; rfl)
      exact ⟨hdummy.1, hdummy.2.1, hdummy.2.2.1⟩
    refine ⟨?_, hmain_noagree.2.1, hmain_noagree.2.2, ?_⟩
    · have := hmain_noagree.1
      simp only [List.length_cons]
      omega
    · intro heq
      have h1 : st1.2.length = gs.length + 1 := by
        have := hmain_noagree.1
        simp only [List.length_cons] at heq
        omega
      have h2 : (rest.foldl stepGate st1).2.length = st1.2.length + rest.length := by
        simp only [List.length_cons] at heq
        omega
      exact (hsub (hagree' hagree h1)).2.2.2 h2

private theorem main :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (11 : ℕ)) (x3 : (Fin (9 : ℕ) → Bool) → Bool),
      PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x5 : Fin (9 : ℕ) → Bool),
            have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))];
            x1.eval (x6 ++ [x6.getD (↑x2) Bool.false]) = x3 x5) →
          (∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.true ∧ x6 (4 : Fin (9 : ℕ)) = Bool.false ∧ x3 x6 ≠ x3 (Function.update x6 (4 : Fin (9 : ℕ)) Bool.true)) →
            have x7 : (Fin (8 : ℕ) → Bool) → Bool := fun (x7 : Fin (8 : ℕ) → Bool) => x3 ![x7 (0 : Fin (8 : ℕ)), x7 (1 : Fin (8 : ℕ)), x7 (2 : Fin (8 : ℕ)), x7 (3 : Fin (8 : ℕ)), Bool.false, x7 (4 : Fin (8 : ℕ)), x7 (5 : Fin (8 : ℕ)), x7 (6 : Fin (8 : ℕ)), x7 (7 : Fin (8 : ℕ))];
            (∃ (x8 : Fin (8 : ℕ) → Bool) (x9 : Fin (8 : ℕ) → Bool), x7 x8 ≠ x7 x9) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x7 (x1.size - (1 : ℕ)) := by
  intro x1 x2 x3 hfan heval hdep
  dsimp only
  intro hnc
  have heval' : ∀ x5 : Fin 9 → Bool, x1.eval (makeInp x5 x2) = x3 x5 := fun x5 => heval x5
  rcases hdep with ⟨x6, h60, h64, h6ne⟩
  rcases hnc with ⟨x8, x9, h89⟩
  have hfold := fold_stepGate_inv x1.gates hfan (env0 x2) []
    (by intro g' hg'; cases hg')
    (by intro i idx hi; simpa using env0_getD_bound x2 i idx hi)
    (fun y => makeInp (pad4 y) x2)
    (fun y => by rw [makeInp_length, env0_length])
    (fun y i => by simpa [runGates] using makeInp_pad4_getD y x2 i)
    (makeInp x6 x2)
    (makeInp (Function.update x6 (4 : Fin 9) true) x2)
    (by rw [makeInp_length, env0_length])
    (by rw [makeInp_length, env0_length])
    (fun i hr => makeInp_agree_of_isRight x6 h60 x2 i hr)
  rcases hfold with ⟨hlen_le, hfan_new, hsem_new, hagree_eq⟩
  set stF := x1.gates.foldl stepGate (env0 x2, [])
  have heval_pad : ∀ y : Fin 8 → Bool,
      x3 (pad4 y) = evalSym (runGates stF.2 (List.ofFn y)) (stF.1.getD x1.output (Sum.inl false)) := by
    intro y
    rw [← heval' (pad4 y)]
    exact hsem_new y x1.output
  cases hout : stF.1.getD x1.output (Sum.inl false) with
  | inl b =>
    have h8 : x3 (pad4 x8) = b := by have := heval_pad x8; rw [hout] at this; exact this
    have h9 : x3 (pad4 x9) = b := by have := heval_pad x9; rw [hout] at this; exact this
    exact False.elim (h89 (h8.trans h9.symm))
  | inr outIdx =>
    have hlt : stF.2.length < x1.gates.length := by
      have hne : stF.2.length ≠ x1.gates.length := by
        intro heq
        have hEqEval : x1.eval (makeInp x6 x2) =
            x1.eval (makeInp (Function.update x6 (4 : Fin 9) true) x2) := by
          exact hagree_eq (by simpa using heq) x1.output (by rw [hout]; rfl)
        have hEq3 : x3 x6 = x3 (Function.update x6 (4 : Fin 9) true) := by
          rw [← heval' x6, ← heval' (Function.update x6 (4 : Fin 9) true)]
          exact hEqEval
        exact h6ne hEq3
      simp only [List.length_nil, Nat.zero_add] at hlen_le
      omega
    refine ⟨⟨stF.2, outIdx⟩, hfan_new, ?_, ?_⟩
    · simp only [Circuit.size]
      omega
    · intro y
      have hy := heval_pad y
      rw [hout] at hy
      exact hy.symm

end PEqualNP.Outside.L_meta_3588

theorem PEqualNP.Outside.L_meta_3588 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (11 : ℕ)) (x3 : (Fin (9 : ℕ) → Bool) → Bool),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))];         x1.eval (x6 ++ [x6.getD (↑x2) Bool.false]) = x3 x5) →       (∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.true ∧ x6 (4 : Fin (9 : ℕ)) = Bool.false ∧ x3 x6 ≠ x3 (Function.update x6 (4 : Fin (9 : ℕ)) Bool.true)) →         have x7 : (Fin (8 : ℕ) → Bool) → Bool := fun (x7 : Fin (8 : ℕ) → Bool) => x3 ![x7 (0 : Fin (8 : ℕ)), x7 (1 : Fin (8 : ℕ)), x7 (2 : Fin (8 : ℕ)), x7 (3 : Fin (8 : ℕ)), Bool.false, x7 (4 : Fin (8 : ℕ)), x7 (5 : Fin (8 : ℕ)), x7 (6 : Fin (8 : ℕ)), x7 (7 : Fin (8 : ℕ))];         (∃ (x8 : Fin (8 : ℕ) → Bool) (x9 : Fin (8 : ℕ) → Bool), x7 x8 ≠ x7 x9) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x7 (x1.size - (1 : ℕ)) :=
  PEqualNP.Outside.L_meta_3588.main
