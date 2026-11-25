import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5464

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def A : Fin 4 → Fin 4 → Bool :=
  fun u v => (18 : ℕ).testBit (4 * u.val + v.val)

private def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

private theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

private theorem witness_rep : Represents A witness := by
  decide

private theorem upper : RepSizeAtMost A 3 :=
  ⟨witness, witness_mono, by decide, witness_rep⟩

private abbrev Vec4 := Bool × Bool × Bool × Bool

private def target : Vec4 := (false, true, true, false)

private def tand (a b : Vec4) : Vec4 :=
  (a.1 && b.1, a.2.1 && b.2.1, a.2.2.1 && b.2.2.1, a.2.2.2 && b.2.2.2)

private def tor (a b : Vec4) : Vec4 :=
  (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2 || b.2.2.2)

private def isInit (v : Vec4) : Prop :=
  v = (false, false, false, false) ∨
  v = (true, true, true, true) ∨
  v = (true, true, false, false) ∨
  v = (false, false, true, true) ∨
  v = (true, false, true, false) ∨
  v = (false, true, false, true)

private theorem tand_self (a : Vec4) : tand a a = a := by
  rcases a with ⟨a0, a1, a2, a3⟩
  simp [tand]

private theorem tor_self (a : Vec4) : tor a a = a := by
  rcases a with ⟨a0, a1, a2, a3⟩
  simp [tor]

private theorem tand_comm (a b : Vec4) : tand a b = tand b a := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp [tand, Bool.and_comm]

private theorem tor_comm (a b : Vec4) : tor a b = tor b a := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp [tor, Bool.or_comm]

private theorem not_isInit_target : ¬ isInit target := by
  simp [isInit, target]

private theorem init_and_target {a b : Vec4} (ha : isInit a) (h : tand a b = target) :
    b = target := by
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [tand, target] at h
  · simpa [tand, target] using h
  · simp [tand, target] at h
  · simp [tand, target] at h
  · simp [tand, target] at h
  · simp [tand, target] at h

private theorem init_or_target {a b : Vec4} (ha : isInit a) (h : tor a b = target) :
    b = target := by
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [tor, target] using h
  · simp [tor, target] at h
  · simp [tor, target] at h
  · simp [tor, target] at h
  · simp [tor, target] at h
  · simp [tor, target] at h

private theorem step_ne_target {v0 a b : Vec4} (hv : v0 ≠ target)
    (ha : a = v0 ∨ isInit a) (hb : b = v0 ∨ isInit b) :
    tand a b ≠ target ∧ tor a b ≠ target := by
  constructor
  · intro h
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rw [tand_self] at h; exact hv h
      · rw [tand_comm] at h; exact hv (init_and_target hb h)
    · rcases hb with rfl | hb
      · exact hv (init_and_target ha h)
      · exact not_isInit_target (init_and_target ha h ▸ hb)
  · intro h
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rw [tor_self] at h; exact hv h
      · rw [tor_comm] at h; exact hv (init_or_target hb h)
    · rcases hb with rfl | hb
      · exact hv (init_or_target ha h)
      · exact not_isInit_target (init_or_target ha h ▸ hb)

private def p00 : List Bool := oneEach (0 : Fin 4) (0 : Fin 4)
private def p01 : List Bool := oneEach (0 : Fin 4) (1 : Fin 4)
private def p10 : List Bool := oneEach (1 : Fin 4) (0 : Fin 4)
private def p11 : List Bool := oneEach (1 : Fin 4) (1 : Fin 4)

private def wvec (gs : List Gate) (i : ℕ) : Vec4 :=
  ((Circuit.wires ⟨gs, 0⟩ p00).getD i false,
   (Circuit.wires ⟨gs, 0⟩ p01).getD i false,
   (Circuit.wires ⟨gs, 0⟩ p10).getD i false,
   (Circuit.wires ⟨gs, 0⟩ p11).getD i false)

private theorem step_getD_lt (x : List Bool) (g : Gate) (i : ℕ) (hi : i < x.length) :
    (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)]).getD i false = x.getD i false :=
  List.getD_append _ _ _ _ hi

private theorem step_getD_eq (x : List Bool) (g : Gate) :
    (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)]).getD x.length false =
      g.op.eval (g.inputs.map fun j => x.getD j false) := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

private theorem step_getD_gt (x : List Bool) (g : Gate) (i : ℕ) (hi : x.length + 1 ≤ i) :
    (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)]).getD i false = false :=
  List.getD_eq_default _ _ (by simp; omega)

private theorem wvec_nil_init (i : ℕ) : isInit (wvec [] i) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact Or.inr (Or.inr (Or.inl (by decide)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · have h0 : p00.length = 8 := by decide
    have h1 : p01.length = 8 := by decide
    have h2 : p10.length = 8 := by decide
    have h3 : p11.length = 8 := by decide
    have hd0 : p00.getD (k + 8) false = false := List.getD_eq_default _ _ (by omega)
    have hd1 : p01.getD (k + 8) false = false := List.getD_eq_default _ _ (by omega)
    have hd2 : p10.getD (k + 8) false = false := List.getD_eq_default _ _ (by omega)
    have hd3 : p11.getD (k + 8) false = false := List.getD_eq_default _ _ (by omega)
    have hw : wvec [] (k + 8) = (false, false, false, false) := by
      simp only [wvec, Circuit.wires, List.foldl_nil, hd0, hd1, hd2, hd3]
    rw [hw]
    exact Or.inl rfl

private theorem gate_eval_pred {P : Vec4 → Prop}
    (h0 : P (false, false, false, false)) (h1 : P (true, true, true, true))
    {g : Gate} (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {x0 x1 x2 x3 : List Bool}
    (hread : ∀ j, P (x0.getD j false, x1.getD j false, x2.getD j false, x3.getD j false)) :
    ∃ a b, P a ∧ P b ∧
      ((g.op.eval (g.inputs.map fun j => x0.getD j false),
        g.op.eval (g.inputs.map fun j => x1.getD j false),
        g.op.eval (g.inputs.map fun j => x2.getD j false),
        g.op.eval (g.inputs.map fun j => x3.getD j false)) = tand a b ∨
       (g.op.eval (g.inputs.map fun j => x0.getD j false),
        g.op.eval (g.inputs.map fun j => x1.getD j false),
        g.op.eval (g.inputs.map fun j => x2.getD j false),
        g.op.eval (g.inputs.map fun j => x3.getD j false)) = tor a b) := by
  rcases hg with ⟨hop, hlen⟩
  rcases h : g.inputs with _ | ⟨i0, _ | ⟨i1, _ | ⟨i2, rest⟩⟩⟩
  · rcases hop with hop | hop
    · refine ⟨(true, true, true, true), (true, true, true, true), h1, h1, Or.inl ?_⟩
      simp [hop, GateOp.eval, tand]
    · refine ⟨(false, false, false, false), (false, false, false, false), h0, h0, Or.inr ?_⟩
      simp [hop, GateOp.eval, tor]
  · refine ⟨(x0.getD i0 false, x1.getD i0 false, x2.getD i0 false, x3.getD i0 false),
      (x0.getD i0 false, x1.getD i0 false, x2.getD i0 false, x3.getD i0 false),
      hread i0, hread i0, ?_⟩
    rcases hop with hop | hop
    · left; simp [hop, GateOp.eval, tand]
    · right; simp [hop, GateOp.eval, tor]
  · refine ⟨(x0.getD i0 false, x1.getD i0 false, x2.getD i0 false, x3.getD i0 false),
      (x0.getD i1 false, x1.getD i1 false, x2.getD i1 false, x3.getD i1 false),
      hread i0, hread i1, ?_⟩
    rcases hop with hop | hop
    · left; simp [hop, GateOp.eval, tand]
    · right; simp [hop, GateOp.eval, tor]
  · simp [h] at hlen

private theorem wvec_len (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
    x.length + gs.length
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

private theorem wvec_one (g0 : Gate)
    (hg0 : (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length ≤ 2) :
    ∃ v0 : Vec4, v0 ≠ target ∧ ∀ i, wvec [g0] i = v0 ∨ isInit (wvec [g0] i) := by
  have hread : ∀ j, isInit (p00.getD j false, p01.getD j false, p10.getD j false, p11.getD j false) := by
    intro j
    simpa only [wvec, Circuit.wires, List.foldl_nil] using wvec_nil_init j
  obtain ⟨a, b, ha, hb, hv0⟩ := gate_eval_pred (Or.inl rfl) (Or.inr (Or.inl rfl)) hg0 hread
  let v0 : Vec4 :=
    (g0.op.eval (g0.inputs.map fun j => p00.getD j false),
     g0.op.eval (g0.inputs.map fun j => p01.getD j false),
     g0.op.eval (g0.inputs.map fun j => p10.getD j false),
     g0.op.eval (g0.inputs.map fun j => p11.getD j false))
  have hv0_ne : v0 ≠ target := by
    have hst := step_ne_target (v0 := (false, false, false, false)) (by decide) (Or.inr ha) (Or.inr hb)
    rcases hv0 with h | h
    · change v0 = tand a b at h; rw [h]; exact hst.1
    · change v0 = tor a b at h; rw [h]; exact hst.2
  refine ⟨v0, hv0_ne, ?_⟩
  intro i
  have h0 : p00.length = 8 := by decide
  have h1 : p01.length = 8 := by decide
  have h2 : p10.length = 8 := by decide
  have h3 : p11.length = 8 := by decide
  by_cases hlt : i < 8
  · have hm : wvec [g0] i = wvec [] i := by
      simp only [wvec, Circuit.wires, List.foldl_cons, List.foldl_nil]
      rw [step_getD_lt _ _ _ (by omega), step_getD_lt _ _ _ (by omega),
          step_getD_lt _ _ _ (by omega), step_getD_lt _ _ _ (by omega)]
    rw [hm]
    exact Or.inr (wvec_nil_init i)
  · by_cases heq : i = 8
    · subst heq
      have hm : wvec [g0] 8 = v0 := by
        simp only [wvec, Circuit.wires, List.foldl_cons, List.foldl_nil, v0]
        rw [← h0, step_getD_eq, h0, ← h1, step_getD_eq, h1,
            ← h2, step_getD_eq, h2, ← h3, step_getD_eq]
      exact Or.inl hm
    · have hm : wvec [g0] i = (false, false, false, false) := by
        simp only [wvec, Circuit.wires, List.foldl_cons, List.foldl_nil]
        rw [step_getD_gt _ _ _ (by omega), step_getD_gt _ _ _ (by omega),
            step_getD_gt _ _ _ (by omega), step_getD_gt _ _ _ (by omega)]
      rw [hm]
      exact Or.inr (Or.inl rfl)

private theorem mono_gate {C : Circuit} (hm : Monotone2 C) (g : Gate) (hg : g ∈ C.gates) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm g hg

private theorem wvec_ne_target_le2 (C : Circuit) (hm : Monotone2 C) (hsz : C.size ≤ 2) :
    wvec C.gates C.output ≠ target := by
  rcases C with ⟨gs, out⟩
  dsimp only at *
  rcases gs with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, rest⟩⟩⟩
  · intro h
    exact not_isInit_target (h ▸ wvec_nil_init out)
  · have hg0 := mono_gate hm g0 (by simp)
    obtain ⟨v0, hv0_ne, hall⟩ := wvec_one g0 hg0
    rcases hall out with h | h
    · rw [h]; exact hv0_ne
    · intro heq; exact not_isInit_target (heq ▸ h)
  · have hg0 := mono_gate hm g0 (by simp)
    have hg1 := mono_gate hm g1 (by simp)
    obtain ⟨v0, hv0_ne, hall⟩ := wvec_one g0 hg0
    let w0 := Circuit.wires ⟨[g0], 0⟩ p00
    let w1 := Circuit.wires ⟨[g0], 0⟩ p01
    let w2 := Circuit.wires ⟨[g0], 0⟩ p10
    let w3 := Circuit.wires ⟨[g0], 0⟩ p11
    have hl0 : w0.length = 9 := by rw [wvec_len, List.length_singleton]; decide
    have hl1 : w1.length = 9 := by rw [wvec_len, List.length_singleton]; decide
    have hl2 : w2.length = 9 := by rw [wvec_len, List.length_singleton]; decide
    have hl3 : w3.length = 9 := by rw [wvec_len, List.length_singleton]; decide
    have hread : ∀ j, (w0.getD j false, w1.getD j false, w2.getD j false, w3.getD j false) = v0 ∨
        isInit (w0.getD j false, w1.getD j false, w2.getD j false, w3.getD j false) := hall
    obtain ⟨c, d, hc, hd, hv1⟩ := gate_eval_pred (P := fun v => v = v0 ∨ isInit v)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) hg1 hread
    have hfold : ∀ x, Circuit.wires ⟨[g0, g1], 0⟩ x =
        Circuit.wires ⟨[g0], 0⟩ x ++ [g1.op.eval (g1.inputs.map fun j => (Circuit.wires ⟨[g0], 0⟩ x).getD j false)] := by
      intro x
      simp only [Circuit.wires, List.foldl_cons, List.foldl_nil]
    by_cases hlt : out < 9
    · have heq : wvec [g0, g1] out = wvec [g0] out := by
        simp only [wvec, hfold]
        rw [step_getD_lt _ _ _ (by change out < w0.length; omega),
            step_getD_lt _ _ _ (by change out < w1.length; omega),
            step_getD_lt _ _ _ (by change out < w2.length; omega),
            step_getD_lt _ _ _ (by change out < w3.length; omega)]
      rw [heq]
      rcases hall out with h | h
      · rw [h]; exact hv0_ne
      · intro ht; exact not_isInit_target (ht ▸ h)
    · by_cases heq9 : out = 9
      · have heq : wvec [g0, g1] out =
            (g1.op.eval (g1.inputs.map fun j => w0.getD j false),
             g1.op.eval (g1.inputs.map fun j => w1.getD j false),
             g1.op.eval (g1.inputs.map fun j => w2.getD j false),
             g1.op.eval (g1.inputs.map fun j => w3.getD j false)) := by
          simp only [wvec, hfold, heq9]
          change ((w0 ++ [_]).getD 9 false, (w1 ++ [_]).getD 9 false,
                  (w2 ++ [_]).getD 9 false, (w3 ++ [_]).getD 9 false) = _
          rw [← hl0, step_getD_eq, hl0, ← hl1, step_getD_eq, hl1,
              ← hl2, step_getD_eq, hl2, ← hl3, step_getD_eq]
        rw [heq]
        have hst := step_ne_target hv0_ne hc hd
        rcases hv1 with h | h
        · rw [h]; exact hst.1
        · rw [h]; exact hst.2
      · have heq : wvec [g0, g1] out = (false, false, false, false) := by
          simp only [wvec, hfold]
          rw [step_getD_gt _ _ _ (by change w0.length + 1 ≤ out; omega),
              step_getD_gt _ _ _ (by change w1.length + 1 ≤ out; omega),
              step_getD_gt _ _ _ (by change w2.length + 1 ≤ out; omega),
              step_getD_gt _ _ _ (by change w3.length + 1 ≤ out; omega)]
        rw [heq]
        decide
  · unfold Circuit.size at hsz
    simp at hsz

private theorem lower : ¬ RepSizeAtMost A 2 := by
  rintro ⟨C, hm, hsz, hrep⟩
  have h00 : (Circuit.wires ⟨C.gates, 0⟩ p00).getD C.output false = false := by
    have h := hrep 0 0
    change (Circuit.wires ⟨C.gates, 0⟩ p00).getD C.output false = A 0 0 at h
    rw [h]; decide
  have h01 : (Circuit.wires ⟨C.gates, 0⟩ p01).getD C.output false = true := by
    have h := hrep 0 1
    change (Circuit.wires ⟨C.gates, 0⟩ p01).getD C.output false = A 0 1 at h
    rw [h]; decide
  have h10 : (Circuit.wires ⟨C.gates, 0⟩ p10).getD C.output false = true := by
    have h := hrep 1 0
    change (Circuit.wires ⟨C.gates, 0⟩ p10).getD C.output false = A 1 0 at h
    rw [h]; decide
  have h11 : (Circuit.wires ⟨C.gates, 0⟩ p11).getD C.output false = false := by
    have h := hrep 1 1
    change (Circuit.wires ⟨C.gates, 0⟩ p11).getD C.output false = A 1 1 at h
    rw [h]; decide
  have ht : wvec C.gates C.output = target := by
    simp only [wvec, target, h00, h01, h10, h11]
  exact wvec_ne_target_le2 C hm hsz ht

private theorem main :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (18 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
      ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (18 : ℕ).testBit (4 * u.val + v.val)) 2 :=
  ⟨upper, lower⟩

end PEqualNP.Outside.L_meta_5464

theorem PEqualNP.Outside.L_meta_5464 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (18 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (18 : ℕ).testBit (4 * u.val + v.val)) 2 := PEqualNP.Outside.L_meta_5464.main
