import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3289

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover


private lemma gateOp_and_eval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
private lemma gateOp_or_eval (l : List Bool) : GateOp.or.eval l = l.any id := rfl

private def runW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma wires_eq_runW (C : Circuit) (x : List Bool) :
    C.wires x = runW C.gates x := rfl

private lemma runW_nil (x : List Bool) : runW [] x = x := rfl

private lemma runW_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    runW (gs ++ [g]) x =
      runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)] := by
  simp [runW]

private lemma runW_len (gs : List Gate) (x : List Bool) :
    (runW gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runW]
  | append_singleton gs g ih =>
    simp [runW_snoc, ih]
    omega

private lemma runW_prefix_getD (g1 g2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + g1.length) :
    (runW (g1 ++ g2) x).getD i false = (runW g1 x).getD i false := by
  induction g2 using List.reverseRecOn with
  | nil => simp
  | append_singleton g2 g ih =>
    rw [← List.append_assoc, runW_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left]
    · rw [← List.getD_eq_getElem?_getD]
      exact ih
    · rw [runW_len, List.length_append]
      omega

private lemma runW_gate_getD (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length) :
    (runW gs x).getD (x.length + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (runW (gs.take k) x).getD i false) := by
  have hsplit : gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  conv_lhs => rw [hsplit]
  have hlenk : (gs.take k).length = k := List.length_take_of_le hk.le
  rw [runW_prefix_getD (gs.take k ++ [gs[k]'hk]) (gs.drop (k + 1)) x (x.length + k)
    (by simp; omega)]
  rw [runW_snoc]
  have hlenw : (runW (gs.take k) x).length = x.length + k := by rw [runW_len, hlenk]
  rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
  rfl

private lemma runW_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hxy : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (runW gs x).getD i false = true → (runW gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact hle
  | append_singleton gs g ih =>
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have ih' := ih hgs'
    have hlen_eq : (runW gs x).length = (runW gs y).length := by rw [runW_len, runW_len, hxy]
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
    intro i hi
    rw [runW_snoc] at hi ⊢
    by_cases hlt : i < (runW gs x).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact ih' i hi
    · by_cases heq : i = (runW gs x).length
      · subst heq
        rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
        rw [hlen_eq, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
        simp only [Option.getD_some] at hi ⊢
        rcases hg with hop | hop <;> rw [hop] at hi ⊢
        · simp only [gateOp_and_eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
          rintro b ⟨j, hj, rfl⟩
          exact ih' j (hi _ ⟨j, hj, rfl⟩)
        · simp only [gateOp_or_eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
          obtain ⟨_, ⟨j, hj, rfl⟩, htrue⟩ := hi
          exact ⟨_, ⟨j, hj, rfl⟩, ih' j htrue⟩
      · have hge : (runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)]).length ≤ i := by
          simp; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hi
        cases hi

private lemma ao2_gate_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {k : ℕ}
    (hk : k < C.gates.length) :
    ((C.gates[k]'hk).op = GateOp.and ∨ (C.gates[k]'hk).op = GateOp.or) ∧
    (C.gates[k]'hk).inputs.length = 2 ∧
    ∀ i ∈ (C.gates[k]'hk).inputs, i < n + k := by
  have hmem := List.getElem_mem hk
  refine ⟨hAO.1 _ hmem, hAO.2.2 _ hmem, ?_⟩
  have hrb := hAO.2.1 k hk
  change ∀ i ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs, i < n + k at hrb
  rw [List.getD_eq_getElem C.gates _ hk] at hrb
  exact hrb

private lemma isAO2_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : List Bool)
    (hx : x.length = n) {k : ℕ} (hk : k < C.gates.length) :
    (C.wires x).getD (n + k) false =
      (C.gates[k]'hk).op.eval
        ((C.gates[k]'hk).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_eq_runW]
  have h := runW_gate_getD C.gates x k hk
  rw [hx] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + k := (ao2_gate_inputs hAO hk).2.2 i hi
  have hlenk : (C.gates.take k).length = k := List.length_take_of_le hk.le
  have hpr := runW_prefix_getD (C.gates.take k) (C.gates.drop k) x i (by rw [hx, hlenk]; exact hi_lt)
  rw [List.take_append_drop] at hpr
  exact hpr.symm

private lemma isAO2_w0_false {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w : ℕ, (C.wires (List.replicate n false)).getD w false = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [wires_eq_runW]
      have hpr := runW_prefix_getD [] C.gates (List.replicate n false) w (by simp; omega)
      rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil]
      simp [List.getD_eq_getElem?_getD, hlt]
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        rw [hwk, isAO2_gate_eval hAO _ (List.length_replicate) hk]
        obtain ⟨hop, hlen, hrb⟩ := ao2_gate_inputs hAO hk
        obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
        have ha : (C.wires (List.replicate n false)).getD a false = false :=
          ih a (by have := hrb a (by rw [hab]; simp); omega)
        have hb : (C.wires (List.replicate n false)).getD b false = false :=
          ih b (by have := hrb b (by rw [hab]; simp); omega)
        rw [hab]
        rcases hop with h | h <;> rw [h]
        · simp only [gateOp_and_eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, ha, hb]; rfl
        · simp only [gateOp_or_eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, ha, hb]; rfl
      · have hge : (C.wires (List.replicate n false)).length ≤ w := by
          rw [wires_eq_runW, runW_len, List.length_replicate]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
        rfl

private def stepR (C : Circuit) (n : ℕ) (a b : ℕ) : Prop :=
  ∃ j : Fin C.size, b = n + j.val ∧ a ∈ (C.gates[j.val]'j.isLt).inputs

private lemma cone_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ {a b : ℕ}, Relation.ReflTransGen (stepR C n) a b → a ≤ b := by
  intro a b hab
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨j, rfl, hin⟩ := hstep
    have hlt := (ao2_gate_inputs hAO j.isLt).2.2 _ hin
    omega

private lemma eval_eq_of_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (o : ℕ)
    (z₁ z₂ : Fin n → Bool)
    (hag : ∀ i : Fin n, Relation.ReflTransGen (stepR C n) i.val o → z₁ i = z₂ i) :
    ∀ w, Relation.ReflTransGen (stepR C n) w o →
      (C.wires (List.ofFn z₁)).getD w false = (C.wires (List.ofFn z₂)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hrw
    by_cases hlt : w < n
    · simp only [wires_eq_runW]
      have h1 := runW_prefix_getD [] C.gates (List.ofFn z₁) w (by simp; omega)
      have h2 := runW_prefix_getD [] C.gates (List.ofFn z₂) w (by simp; omega)
      rw [show C.gates = [] ++ C.gates from rfl, h1, h2, runW_nil, runW_nil]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
      exact hag ⟨w, hlt⟩ hrw
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        rw [hwk, isAO2_gate_eval hAO _ List.length_ofFn hk,
            isAO2_gate_eval hAO _ List.length_ofFn hk]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hi_lt : i < n + k := (ao2_gate_inputs hAO hk).2.2 i hi
        have hri : Relation.ReflTransGen (stepR C n) i o :=
          Relation.ReflTransGen.head ⟨⟨k, hk⟩, rfl, hi⟩ (hwk ▸ hrw)
        exact ih i (by omega) hri
      · have hge1 : (C.wires (List.ofFn z₁)).length ≤ w := by
          rw [wires_eq_runW, runW_len, List.length_ofFn]; omega
        have hge2 : (C.wires (List.ofFn z₂)).length ≤ w := by
          rw [wires_eq_runW, runW_len, List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]

private lemma wires_mono_of_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (z₁ z₂ : Fin n → Bool) (hle : ∀ i : Fin n, z₁ i = true → z₂ i = true) :
    ∀ w, (C.wires (List.ofFn z₁)).getD w false = true →
      (C.wires (List.ofFn z₂)).getD w false = true := by
  apply runW_mono C.gates (fun g hg => hAO.1 g hg) (List.ofFn z₁) (List.ofFn z₂) (by simp)
  intro i hi
  by_cases hlt : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
    exact hle ⟨i, hlt⟩ hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
    cases hi



private lemma reduce_to_AO2 (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hmono : Monotone2 C)
    (hsound : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false)
    (ET : Finset (Fin N × Fin N))
    (hET : ∀ e ∈ ET, I e.1 e.2 ∧
      circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
    (hET_ne : ET.Nonempty) :
    ∃ C1 : Circuit, IsAO2 (N + N) C1 ∧ C1.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C1 z = true → circuitFun (N + N) C z = true) ∧
      (∀ e ∈ ET, circuitFun (N + N) C1
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) := by
  classical
  let n : ℕ := N + N
  let edge : Fin N → Fin N → Fin n → Bool := fun p l i =>
    decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
  obtain ⟨e₀, he₀⟩ := hET_ne
  have hC_ao : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases (hmono g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hw0_le : ∀ z : Fin n → Bool, ∀ w,
      (C.wires (List.replicate n false)).getD w false = true →
      (C.wires (List.ofFn z)).getD w false = true := by
    intro z w hw
    exact runW_mono C.gates hC_ao (List.replicate n false) (List.ofFn z) (by simp)
      (fun i hi => by
        by_cases hlt : i < n
        · simp [List.getD_eq_getElem?_getD, hlt] at hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          cases hi) w hw
  have hw0_out : (C.wires (List.replicate n false)).getD C.output false = false := by
    have h0 : circuitFun n C (fun _ => false) = false := by
      apply hsound (fun _ => false)
      · simp
      · rintro ⟨_, _, _, h, _⟩
        cases h
    have hrep : List.ofFn (fun _ : Fin n => false) = List.replicate n false := List.ofFn_const _ _
    change (C.wires (List.ofFn (fun _ : Fin n => false))).getD C.output false = false at h0
    rwa [hrep] at h0
  let w0 : ℕ → Bool := fun w => (C.wires (List.replicate n false)).getD w false
  let wpl : Fin N → Fin N → ℕ → Bool := fun p l w => (C.wires (List.ofFn (edge p l))).getD w false
  let evalTag : List Bool → Bool ⊕ ℕ → Bool := fun ws t =>
    Sum.elim id (fun i => ws.getD i false) t
  let toOpt : Bool ⊕ ℕ → Option ℕ := Sum.elim (fun _ => none) some
  let step : (List Gate × (ℕ → Bool ⊕ ℕ)) → ℕ → (List Gate × (ℕ → Bool ⊕ ℕ)) := fun st k =>
    let gs := st.1
    let mp := st.2
    if w0 (n + k) = true then
      (gs, Function.update mp (n + k) (Sum.inl true))
    else if ¬ ∃ e ∈ ET, wpl e.1 e.2 (n + k) = true then
      (gs, Function.update mp (n + k) (Sum.inl false))
    else
      let g := C.gates.getD k ⟨GateOp.or, []⟩
      let tagOf : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then mp i else Sum.inl false
      let ws : List ℕ := g.inputs.filterMap (fun i => toOpt (tagOf i))
      if ws.length = 1 then
        (gs, Function.update mp (n + k) (Sum.inr (ws.getD 0 0)))
      else if ws.length = 2 then
        (gs ++ [Gate.mk g.op [ws.getD 0 0, ws.getD 1 0]], Function.update mp (n + k) (Sum.inr (n + gs.length)))
      else
        (gs, Function.update mp (n + k) (Sum.inl false))
  let build : ℕ → (List Gate × (ℕ → Bool ⊕ ℕ)) := fun k =>
    (List.range k).foldl step ([], Sum.inr)
  have hbuild_succ : ∀ k, build (k + 1) = step (build k) k := by
    intro k
    simp [build, List.range_succ]
  have hInv : ∀ k ≤ C.gates.length,
      let st := build k
      let gs := st.1
      let mp := st.2
      gs.length ≤ k ∧
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
      (∀ w < n + k, Sum.elim (fun _ => True) (fun i => i < n + gs.length) (mp w)) ∧
      (∀ w < n + k, mp w = Sum.inl true → w0 w = true) ∧
      (∀ (z : Fin n → Bool) (w : ℕ), w < n + k →
        evalTag (runW gs (List.ofFn z)) (mp w) = true → (C.wires (List.ofFn z)).getD w false = true) ∧
      (∀ e ∈ ET, ∀ w < n + k,
        evalTag (runW gs (List.ofFn (edge e.1 e.2))) (mp w) = wpl e.1 e.2 w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp [build], by simp [build], by simp [build], ?_, ?_, ?_, ?_⟩
      · intro w hw
        simpa [build] using hw
      · intro w _ h
        simp [build] at h
      · intro z w hw hev
        simp only [build, List.range_zero, List.foldl_nil, evalTag, runW_nil] at hev
        have hpr := runW_prefix_getD [] C.gates (List.ofFn z) w (by simp; omega)
        rw [wires_eq_runW, show C.gates = [] ++ C.gates from rfl, hpr, runW_nil]
        exact hev
      · intro e _ w hw
        simp only [build, List.range_zero, List.foldl_nil, evalTag, runW_nil]
        have hpr := runW_prefix_getD [] C.gates (List.ofFn (edge e.1 e.2)) w (by simp; omega)
        change (List.ofFn (edge e.1 e.2)).getD w false = (runW C.gates (List.ofFn (edge e.1 e.2))).getD w false
        rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil]
    | succ k ih =>
      intro hk
      obtain ⟨hsz, hao, hrb, hbd, htr, hup, hex⟩ := ih (Nat.le_of_succ_le hk)
      set gs := (build k).1
      set mp := (build k).2
      have hklt : k < C.gates.length := Nat.lt_of_succ_le hk
      have hsz_le : gs.length ≤ k + 1 := by omega
      rw [hbuild_succ]
      change let st := step (gs, mp) k; _
      by_cases hw0k : w0 (n + k) = true
      · have hst : step (gs, mp) k = (gs, Function.update mp (n + k) (Sum.inl true)) := by
          simp [step, hw0k]
        rw [hst]
        dsimp only
        refine ⟨hsz_le, hao, hrb, ?_, ?_, ?_, ?_⟩
        · intro w hw
          by_cases hwk : w = n + k
          · subst hwk; simp
          · rw [Function.update_of_ne hwk]; exact hbd w (by omega)
        · intro w hw h1
          by_cases hwk : w = n + k
          · subst hwk; exact hw0k
          · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
        · intro z w hw hev
          by_cases hwk : w = n + k
          · subst hwk; exact hw0_le z (n + k) hw0k
          · rw [Function.update_of_ne hwk] at hev; exact hup z w (by omega) hev
        · intro e he w hw
          by_cases hwk : w = n + k
          · subst hwk
            simp only [Function.update_self, evalTag]
            exact (hw0_le (edge e.1 e.2) (n + k) hw0k).symm
          · rw [Function.update_of_ne hwk]; exact hex e he w (by omega)
      · have hw0kf : w0 (n + k) = false := Bool.eq_false_iff.mpr hw0k
        by_cases hact : ∃ e ∈ ET, wpl e.1 e.2 (n + k) = true
        · set g := C.gates.getD k ⟨GateOp.or, []⟩
          have hg_eq : g = C.gates[k]'hklt := List.getD_eq_getElem C.gates _ hklt
          have hg_mem : g ∈ C.gates := hg_eq ▸ List.getElem_mem hklt
          have hg_ao : g.op = GateOp.and ∨ g.op = GateOp.or := hC_ao g hg_mem
          have hg_len : g.inputs.length ≤ 2 := (hmono g hg_mem).2
          let tagOf : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then mp i else Sum.inl false
          have htag_bd : ∀ i w, tagOf i = Sum.inr w → w < n + gs.length := by
            intro i w htw
            by_cases hi : i < n + k
            · have hb := hbd i hi
              simp only [tagOf, hi, ↓reduceIte] at htw
              rw [htw] at hb
              exact hb
            · simp [tagOf, hi] at htw
          have htag_tr : ∀ i, tagOf i = Sum.inl true → i < n + k ∧ w0 i = true := by
            intro i hti
            by_cases hi : i < n + k
            · simp only [tagOf, hi, ↓reduceIte] at hti
              exact ⟨hi, htr i hi hti⟩
            · simp [tagOf, hi] at hti
          have htag_up : ∀ (z : Fin n → Bool) (i : ℕ),
              evalTag (runW gs (List.ofFn z)) (tagOf i) = true →
              (runW (C.gates.take k) (List.ofFn z)).getD i false = true := by
            intro z i hev
            by_cases hi : i < n + k
            · simp only [tagOf, hi, ↓reduceIte] at hev
              have hc := hup z i hi hev
              have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
              have hpr := runW_prefix_getD (C.gates.take k) (C.gates.drop k) (List.ofFn z) i
                (by simp [hlenk]; omega)
              rw [List.take_append_drop] at hpr
              rw [← hpr]
              exact hc
            · simp [tagOf, hi, evalTag] at hev
          have htag_ex : ∀ e ∈ ET, ∀ i : ℕ,
              evalTag (runW gs (List.ofFn (edge e.1 e.2))) (tagOf i) =
              (runW (C.gates.take k) (List.ofFn (edge e.1 e.2))).getD i false := by
            intro e he i
            by_cases hi : i < n + k
            · simp only [tagOf, hi, ↓reduceIte]
              rw [hex e he i hi]
              have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
              have hpr := runW_prefix_getD (C.gates.take k) (C.gates.drop k) (List.ofFn (edge e.1 e.2)) i
                (by simp [hlenk]; omega)
              rw [List.take_append_drop] at hpr
              exact hpr
            · simp only [tagOf, hi, ↓reduceIte, evalTag]
              have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
              have hge : (runW (C.gates.take k) (List.ofFn (edge e.1 e.2))).length ≤ i := by
                rw [runW_len, List.length_ofFn, hlenk]; omega
              symm
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
              rfl
          have hC_eval_z : ∀ (z : Fin n → Bool),
              (C.wires (List.ofFn z)).getD (n + k) false =
              g.op.eval (g.inputs.map fun i => (runW (C.gates.take k) (List.ofFn z)).getD i false) := by
            intro z
            have h := runW_gate_getD C.gates (List.ofFn z) k hklt
            rw [List.length_ofFn] at h
            rw [← hg_eq] at h
            exact h
          have hC_eval_0 : w0 (n + k) =
              g.op.eval (g.inputs.map fun i => (runW (C.gates.take k) (List.replicate n false)).getD i false) := by
            have h := runW_gate_getD C.gates (List.replicate n false) k hklt
            rw [List.length_replicate] at h
            rw [← hg_eq] at h
            exact h
          have hC_take_0 : ∀ i < n + k,
              (runW (C.gates.take k) (List.replicate n false)).getD i false = w0 i := by
            intro i hi
            have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
            have hpr := runW_prefix_getD (C.gates.take k) (C.gates.drop k) (List.replicate n false) i
              (by simp [hlenk]; omega)
            rw [List.take_append_drop] at hpr
            exact hpr.symm
          obtain ⟨e₁, he₁, hw₁⟩ := hact
          have hC_eval_1 : g.op.eval (g.inputs.map fun i => evalTag (runW gs (List.ofFn (edge e₁.1 e₁.2))) (tagOf i)) = true := by
            have heq : (g.inputs.map fun i => evalTag (runW gs (List.ofFn (edge e₁.1 e₁.2))) (tagOf i)) =
                (g.inputs.map fun i => (runW (C.gates.take k) (List.ofFn (edge e₁.1 e₁.2))).getD i false) :=
              List.map_congr_left (fun i _ => htag_ex e₁ he₁ i)
            rw [heq, ← hC_eval_z (edge e₁.1 e₁.2)]
            exact hw₁
          set ws : List ℕ := g.inputs.filterMap (fun i => toOpt (tagOf i))
          have hws_not_nil : ws ≠ [] := by
            intro hnil
            have hall_inl : ∀ i ∈ g.inputs, ∃ b : Bool, tagOf i = Sum.inl b := by
              intro i hi
              cases ht : tagOf i with
              | inl b => exact ⟨b, rfl⟩
              | inr w =>
                have hmem : w ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                rw [hnil] at hmem
                simp at hmem
            rcases hg_ao with hop | hop
            · rw [hop] at hC_eval_1 hC_eval_0
              have hall_t : ∀ i ∈ g.inputs, tagOf i = Sum.inl true := by
                intro i hi
                obtain ⟨b, hb⟩ := hall_inl i hi
                cases b
                · simp only [gateOp_and_eval, List.all_eq_true, List.mem_map, id_eq] at hC_eval_1
                  have hff := hC_eval_1 _ ⟨i, hi, rfl⟩
                  simp [hb, evalTag] at hff
                · exact hb
              have h0t : w0 (n + k) = true := by
                rw [hC_eval_0]
                simp only [gateOp_and_eval, List.all_eq_true, List.mem_map, id_eq]
                rintro _ ⟨i, hi, rfl⟩
                obtain ⟨hlti, hw0i⟩ := htag_tr i (hall_t i hi)
                rw [hC_take_0 i hlti]
                exact hw0i
              rw [hw0kf] at h0t
              cases h0t
            · rw [hop] at hC_eval_1 hC_eval_0
              simp only [gateOp_or_eval, List.any_eq_true, List.mem_map, id_eq] at hC_eval_1
              obtain ⟨_, ⟨i, hi, rfl⟩, htrue⟩ := hC_eval_1
              obtain ⟨b, hb⟩ := hall_inl i hi
              cases b
              · simp [hb, evalTag] at htrue
              · obtain ⟨hlti, hw0i⟩ := htag_tr i hb
                have h0t : w0 (n + k) = true := by
                  rw [hC_eval_0]
                  simp only [gateOp_or_eval, List.any_eq_true, List.mem_map, id_eq]
                  exact ⟨_, ⟨i, hi, rfl⟩, by rw [hC_take_0 i hlti]; exact hw0i⟩
                rw [hw0kf] at h0t
                cases h0t
          have hws_len : ws.length ≤ 2 := (List.length_filterMap_le _ _).trans hg_len
          have hws_cases : (∃ a, ws = [a]) ∨ (∃ a b, ws = [a, b]) := by
            rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · exact absurd rfl hws_not_nil
            · exact Or.inl ⟨a, rfl⟩
            · exact Or.inr ⟨a, b, rfl⟩
            · simp at hws_len
          rcases hws_cases with ⟨a, hwa⟩ | ⟨a, b, hwab⟩
          · have hst_a : step (gs, mp) k = (gs, Function.update mp (n + k) (Sum.inr a)) := by
              have hact' : ∃ e ∈ ET, wpl e.1 e.2 (n + k) = true := ⟨e₁, he₁, hw₁⟩
              simp only [step, hw0kf, Bool.false_eq_true, ↓reduceIte, hact', not_true_eq_false]
              change (if ws.length = 1 then (gs, Function.update mp (n + k) (Sum.inr (ws.getD 0 0)))
                else if ws.length = 2 then (gs ++ [Gate.mk g.op [ws.getD 0 0, ws.getD 1 0]],
                  Function.update mp (n + k) (Sum.inr (n + gs.length)))
                else (gs, Function.update mp (n + k) (Sum.inl false))) = _
              rw [hwa]
              rfl
            rw [hst_a]
            dsimp only
            have ha_mem : a ∈ ws := by rw [hwa]; simp
            obtain ⟨ia, hia_mem, hia_tag⟩ := List.mem_filterMap.mp ha_mem
            have hia_inr : tagOf ia = Sum.inr a := by
              cases ht : tagOf ia with
              | inl _ => simp [ht, toOpt] at hia_tag
              | inr w =>
                simp only [ht, toOpt, Sum.elim_inr, Option.some.injEq] at hia_tag
                exact congrArg Sum.inr hia_tag
            have ha_lt : a < n + gs.length := htag_bd ia a hia_inr
            refine ⟨hsz_le, hao, hrb, ?_, ?_, ?_, ?_⟩
            · intro w hw
              by_cases hwk : w = n + k
              · subst hwk; simpa using ha_lt
              · rw [Function.update_of_ne hwk]; exact hbd w (by omega)
            · intro w hw h1
              by_cases hwk : w = n + k
              · subst hwk; simp at h1
              · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
            · intro z w hw hev
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr] at hev
                rw [hC_eval_z z]
                rcases hg_ao with hop | hop <;> rw [hop]
                · simp only [gateOp_and_eval, List.all_eq_true, List.mem_map, id_eq]
                  rintro _ ⟨i, hi, rfl⟩
                  cases ht : tagOf i with
                  | inl b =>
                    cases b
                    · rw [hop] at hC_eval_1
                      simp only [gateOp_and_eval, List.all_eq_true, List.mem_map, id_eq] at hC_eval_1
                      have hf := hC_eval_1 _ ⟨i, hi, rfl⟩
                      simp [ht, evalTag] at hf
                    · exact htag_up z i (by simp [ht, evalTag])
                  | inr w' =>
                    have hw'mem : w' ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                    rw [hwa, List.mem_singleton] at hw'mem
                    subst hw'mem
                    exact htag_up z i (by simp only [ht, evalTag, Sum.elim_inr]; exact hev)
                · simp only [gateOp_or_eval, List.any_eq_true, List.mem_map, id_eq]
                  exact ⟨_, ⟨ia, hia_mem, rfl⟩, htag_up z ia (by simp only [hia_inr, evalTag, Sum.elim_inr]; exact hev)⟩
              · rw [Function.update_of_ne hwk] at hev; exact hup z w (by omega) hev
            · intro e he w hw
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr]
                rw [show wpl e.1 e.2 (n + k) = (C.wires (List.ofFn (edge e.1 e.2))).getD (n + k) false from rfl]
                rw [hC_eval_z (edge e.1 e.2)]
                have hmap : (g.inputs.map fun i => (runW (C.gates.take k) (List.ofFn (edge e.1 e.2))).getD i false) =
                    (g.inputs.map fun i => evalTag (runW gs (List.ofFn (edge e.1 e.2))) (tagOf i)) :=
                  List.map_congr_left (fun i _ => (htag_ex e he i).symm)
                rw [hmap]
                rcases hg_ao with hop | hop <;> rw [hop]
                · apply Bool.eq_iff_iff.mpr
                  simp only [gateOp_and_eval, List.all_eq_true, List.mem_map, id_eq]
                  constructor
                  · rintro ha_t _ ⟨i, hi, rfl⟩
                    cases ht : tagOf i with
                    | inl b =>
                      cases b
                      · rw [hop] at hC_eval_1
                        simp only [gateOp_and_eval, List.all_eq_true, List.mem_map, id_eq] at hC_eval_1
                        have hf := hC_eval_1 _ ⟨i, hi, rfl⟩
                        simp [ht, evalTag] at hf
                      · rfl
                    | inr w' =>
                      have hw'mem : w' ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                      rw [hwa, List.mem_singleton] at hw'mem
                      subst hw'mem
                      exact ha_t
                  · intro hall
                    have h1 := hall _ ⟨ia, hia_mem, rfl⟩
                    simpa [hia_inr, evalTag] using h1
                · apply Bool.eq_iff_iff.mpr
                  simp only [gateOp_or_eval, List.any_eq_true, List.mem_map, id_eq]
                  constructor
                  · intro ha_t
                    exact ⟨_, ⟨ia, hia_mem, rfl⟩, by simpa [hia_inr, evalTag] using ha_t⟩
                  · rintro ⟨_, ⟨i, hi, rfl⟩, htrue⟩
                    cases ht : tagOf i with
                    | inl b =>
                      cases b
                      · simp [ht, evalTag] at htrue
                      · obtain ⟨hlti, hw0i⟩ := htag_tr i ht
                        have h0t : w0 (n + k) = true := by
                          rw [hC_eval_0, hop]
                          simp only [gateOp_or_eval, List.any_eq_true, List.mem_map, id_eq]
                          exact ⟨_, ⟨i, hi, rfl⟩, by rw [hC_take_0 i hlti]; exact hw0i⟩
                        rw [hw0kf] at h0t
                        cases h0t
                    | inr w' =>
                      have hw'mem : w' ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                      rw [hwa, List.mem_singleton] at hw'mem
                      subst hw'mem
                      simpa [ht, evalTag] using htrue
              · rw [Function.update_of_ne hwk]; exact hex e he w (by omega)
          · have hst_ab : step (gs, mp) k =
                (gs ++ [Gate.mk g.op [a, b]], Function.update mp (n + k) (Sum.inr (n + gs.length))) := by
              have hact' : ∃ e ∈ ET, wpl e.1 e.2 (n + k) = true := ⟨e₁, he₁, hw₁⟩
              simp only [step, hw0kf, Bool.false_eq_true, ↓reduceIte, hact', not_true_eq_false]
              change (if ws.length = 1 then (gs, Function.update mp (n + k) (Sum.inr (ws.getD 0 0)))
                else if ws.length = 2 then (gs ++ [Gate.mk g.op [ws.getD 0 0, ws.getD 1 0]],
                  Function.update mp (n + k) (Sum.inr (n + gs.length)))
                else (gs, Function.update mp (n + k) (Sum.inl false))) = _
              rw [hwab]
              rfl
            rw [hst_ab]
            dsimp only
            have hlen_inp : g.inputs.length = 2 := by
              have h1 := List.length_filterMap_le (fun i => toOpt (tagOf i)) g.inputs
              change ws.length ≤ g.inputs.length at h1
              rw [hwab] at h1
              simp at h1
              omega
            obtain ⟨i₀, i₁, hinp⟩ := List.length_eq_two.mp hlen_inp
            have hi₀₁ : tagOf i₀ = Sum.inr a ∧ tagOf i₁ = Sum.inr b := by
              have hfm : ws = [a, b] := hwab
              dsimp only [ws] at hfm
              rw [hinp] at hfm
              cases h0 : tagOf i₀ <;> cases h1 : tagOf i₁ <;> simp [h0, h1, toOpt] at hfm
              obtain ⟨rfl, rfl⟩ := hfm
              exact ⟨rfl, rfl⟩
            have ha_lt : a < n + gs.length := htag_bd i₀ a hi₀₁.1
            have hb_lt : b < n + gs.length := htag_bd i₁ b hi₀₁.2
            have hrun_keep : ∀ (x : List Bool) (w : ℕ), x.length = n → w < n + gs.length →
                (runW (gs ++ [⟨g.op, [a, b]⟩]) x).getD w false = (runW gs x).getD w false := by
              intro x w hx hw
              rw [runW_prefix_getD gs [⟨g.op, [a, b]⟩] x w (by omega)]
            have hrun_new : ∀ (x : List Bool), x.length = n →
                (runW (gs ++ [⟨g.op, [a, b]⟩]) x).getD (n + gs.length) false =
                g.op.eval [(runW gs x).getD a false, (runW gs x).getD b false] := by
              intro x hx
              rw [runW_snoc]
              have hlenw : (runW gs x).length = n + gs.length := by rw [runW_len, hx]
              rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
              rfl
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [List.length_append, List.length_singleton]
              omega
            · intro g' hg'
              simp only [List.mem_append, List.mem_singleton] at hg'
              rcases hg' with hg' | rfl
              · exact hao g' hg'
              · exact ⟨hg_ao, rfl⟩
            · intro j hj i hi
              simp only [List.length_append, List.length_singleton] at hj
              by_cases hjlt : j < gs.length
              · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt, ← List.getD_eq_getElem?_getD] at hi
                exact hrb j hjlt i hi
              · have hjeq : j = gs.length := by omega
                subst hjeq
                rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
                simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact ha_lt
                · exact hb_lt
            · intro w hw
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, Sum.elim_inr, List.length_append, List.length_singleton]
                omega
              · rw [Function.update_of_ne hwk]
                have hb := hbd w (by omega)
                cases hm : mp w with
                | inl _ => simp
                | inr u =>
                  rw [hm] at hb
                  simp only [Sum.elim_inr] at hb ⊢
                  simp only [List.length_append, List.length_singleton]
                  omega
            · intro w hw h1
              by_cases hwk : w = n + k
              · subst hwk; simp at h1
              · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
            · intro z w hw hev
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr] at hev
                rw [hrun_new (List.ofFn z) (by simp)] at hev
                rw [hC_eval_z z, hinp]
                simp only [List.map_cons, List.map_nil]
                rcases hg_ao with hop | hop <;> rw [hop] at hev ⊢
                · simp only [gateOp_and_eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hev ⊢
                  exact ⟨htag_up z i₀ (by simp only [hi₀₁.1, evalTag, Sum.elim_inr]; exact hev.1),
                    htag_up z i₁ (by simp only [hi₀₁.2, evalTag, Sum.elim_inr]; exact hev.2)⟩
                · simp only [gateOp_or_eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hev ⊢
                  rcases hev with h0 | h1
                  · exact Or.inl (htag_up z i₀ (by simp only [hi₀₁.1, evalTag, Sum.elim_inr]; exact h0))
                  · exact Or.inr (htag_up z i₁ (by simp only [hi₀₁.2, evalTag, Sum.elim_inr]; exact h1))
              · rw [Function.update_of_ne hwk] at hev
                apply hup z w (by omega)
                cases hm : mp w with
                | inl b => simpa [hm, evalTag] using hev
                | inr u =>
                  have hu := hbd w (by omega)
                  rw [hm] at hu hev
                  simp only [Sum.elim_inr] at hu
                  simp only [evalTag, Sum.elim_inr] at hev ⊢
                  rwa [hrun_keep (List.ofFn z) u (by simp) hu] at hev
            · intro e he w hw
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr]
                rw [hrun_new (List.ofFn (edge e.1 e.2)) (by simp [n])]
                rw [show wpl e.1 e.2 (n + k) = (C.wires (List.ofFn (edge e.1 e.2))).getD (n + k) false from rfl]
                rw [hC_eval_z (edge e.1 e.2), hinp]
                simp only [List.map_cons, List.map_nil]
                have e0 := htag_ex e he i₀
                have e1 := htag_ex e he i₁
                simp only [hi₀₁.1, hi₀₁.2, evalTag, Sum.elim_inr] at e0 e1
                rw [e0, e1]
              · rw [Function.update_of_ne hwk]
                rw [← hex e he w (by omega)]
                cases hm : mp w with
                | inl _ => rfl
                | inr u =>
                  have hu := hbd w (by omega)
                  rw [hm] at hu
                  simp only [Sum.elim_inr] at hu
                  simp only [evalTag, Sum.elim_inr]
                  exact hrun_keep (List.ofFn (edge e.1 e.2)) u (by simp [n]) hu
        · have hst : step (gs, mp) k = (gs, Function.update mp (n + k) (Sum.inl false)) := by
            change (if w0 (n + k) = true then _ else if ¬ ∃ e ∈ ET, wpl e.1 e.2 (n + k) = true then _ else _) = _
            rw [if_neg hw0k, if_pos hact]
          rw [hst]
          dsimp only
          refine ⟨hsz_le, hao, hrb, ?_, ?_, ?_, ?_⟩
          · intro w hw
            by_cases hwk : w = n + k
            · subst hwk; simp
            · rw [Function.update_of_ne hwk]; exact hbd w (by omega)
          · intro w hw h1
            by_cases hwk : w = n + k
            · subst hwk; simp at h1
            · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
          · intro z w hw hev
            by_cases hwk : w = n + k
            · subst hwk; simp [evalTag] at hev
            · rw [Function.update_of_ne hwk] at hev; exact hup z w (by omega) hev
          · intro e he w hw
            by_cases hwk : w = n + k
            · subst hwk
              simp only [Function.update_self, evalTag]
              cases hval : wpl e.1 e.2 (n + k)
              · rfl
              · exact absurd ⟨e, he, hval⟩ hact
            · rw [Function.update_of_ne hwk]; exact hex e he w (by omega)
  obtain ⟨hsz, hao, hrb, _, htr, hup, hex⟩ := hInv C.gates.length le_rfl
  set gs := (build C.gates.length).1
  set mp := (build C.gates.length).2
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have hge' : (C.wires (List.ofFn (edge e₀.1 e₀.2))).length ≤ C.output := by
      rw [wires_eq_runW, runW_len, List.length_ofFn]
      omega
    have hf : circuitFun n C (edge e₀.1 e₀.2) = false := by
      change (C.wires (List.ofFn (edge e₀.1 e₀.2))).getD C.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge']
      rfl
    have ht := (hET e₀ he₀).2
    rw [hf] at ht
    cases ht
  have hout_tag : ∃ o₁ : ℕ, mp C.output = Sum.inr o₁ := by
    cases hm : mp C.output with
    | inl b =>
      cases b
      · have he := hex e₀ he₀ C.output hout_lt
        rw [hm] at he
        simp only [evalTag] at he
        have ht := (hET e₀ he₀).2
        change wpl e₀.1 e₀.2 C.output = true at ht
        rw [ht] at he
        cases he
      · have h0 := htr C.output hout_lt hm
        rw [show w0 C.output = false from hw0_out] at h0
        cases h0
    | inr o₁ => exact ⟨o₁, rfl⟩
  obtain ⟨o₁, ho₁_eq⟩ := hout_tag
  refine ⟨⟨gs, o₁⟩, ?_, hsz, ?_, ?_⟩
  · refine ⟨fun g hg => (hao g hg).1, ?_, fun g hg => (hao g hg).2⟩
    intro j hj i hi
    exact hrb j hj i hi
  · intro z hz
    have hev : evalTag (runW gs (List.ofFn z)) (mp C.output) = true := by
      rw [ho₁_eq]
      exact hz
    exact hup z C.output hout_lt hev
  · intro e he
    have hex' := hex e he C.output hout_lt
    rw [ho₁_eq] at hex'
    change circuitFun n ⟨gs, o₁⟩ (edge e.1 e.2) = circuitFun n C (edge e.1 e.2) at hex'
    rw [hex']
    exact (hET e he).2



private lemma plane_four_free (N : ℕ) (I : Fin N → Fin N → Prop)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l') := by
  intro p p' l l' hpp hll ⟨h11, h21, h12, h22⟩
  obtain ⟨lstar, _, huniq'⟩ := huniq p p' hpp
  exact hll ((huniq' l ⟨h11, h21⟩).trans (huniq' l' ⟨h12, h22⟩).symm)

private lemma plane_pt_deg (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l).card = q + 1 := by
  classical
  have hfour := plane_four_free N I huniq
  intro p
  let Lp := Finset.univ.filter fun l : Fin N => I p l
  have hpart : (Finset.univ.erase p : Finset (Fin N)) =
      Lp.biUnion (fun l => (Finset.univ.filter fun p' : Fin N => I p' l).erase p) := by
    ext p'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, Lp,
      Finset.mem_filter, true_and]
    constructor
    · intro hne
      obtain ⟨l, ⟨hp1, hp2⟩, _⟩ := huniq p p' hne.symm
      exact ⟨l, hp1, hne, hp2⟩
    · rintro ⟨_, _, hne, _⟩
      exact hne
  have hdisj : Set.PairwiseDisjoint (↑Lp) (fun l => (Finset.univ.filter fun p' : Fin N => I p' l).erase p) := by
    intro l₁ hl₁ l₂ hl₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p' hp1 hp2
    have h1 := Finset.mem_erase.mp hp1
    have h2 := Finset.mem_erase.mp hp2
    exact hfour p p' l₁ l₂ h1.1.symm hne
      ⟨(Finset.mem_filter.mp hl₁).2, (Finset.mem_filter.mp h1.2).2,
       (Finset.mem_filter.mp hl₂).2, (Finset.mem_filter.mp h2.2).2⟩
  have hcard_eq := congrArg Finset.card hpart
  rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin,
    Finset.card_biUnion hdisj] at hcard_eq
  have hsum_q : ∑ l ∈ Lp, ((Finset.univ.filter fun p' : Fin N => I p' l).erase p).card = Lp.card * q := by
    have heach : ∀ l ∈ Lp, ((Finset.univ.filter fun p' : Fin N => I p' l).erase p).card = q := by
      intro l hl
      have hmem : p ∈ Finset.univ.filter (fun p' : Fin N => I p' l) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
      rw [Finset.card_erase_of_mem hmem]
      have hc := hcol l
      rw [Fintype.card_subtype] at hc
      omega
    rw [Finset.sum_congr rfl heach]
    simp
  rw [hsum_q] at hcard_eq
  have hN1 : N - 1 = (q + 1) * q := by rw [hN, Nat.add_sub_cancel]; ring
  rw [hN1] at hcard_eq
  exact Nat.eq_of_mul_eq_mul_right hq hcard_eq.symm

private lemma tree_bound (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l'))
    (C : Circuit) (hAO : IsAO2 (N + N) C) (o : ℕ) (ho_lt : o < N + N + C.gates.length)
    (huniq_read : ∀ w < o, Relation.ReflTransGen (stepR C (N + N)) w o →
      ∀ j₁ j₂ : Fin C.size, ∀ b₁ b₂ : Fin 2,
        Relation.ReflTransGen (stepR C (N + N)) (N + N + j₁.val) o →
        Relation.ReflTransGen (stepR C (N + N)) (N + N + j₂.val) o →
        (C.gates[j₁.val]'j₁.isLt).inputs.getD b₁.val 0 = w →
        (C.gates[j₂.val]'j₂.isLt).inputs.getD b₂.val 0 = w →
        j₁ = j₂ ∧ b₁ = b₂)
    (hsound_p : ∀ p : Fin N,
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)))).getD o false = false)
    (hsound_l : ∀ l : Fin N,
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)))).getD o false = false)
    (hsound_edge : ∀ p l : Fin N,
      Relation.ReflTransGen (stepR C (N + N)) p.val o →
      Relation.ReflTransGen (stepR C (N + N)) (N + l.val) o →
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD o false = true →
      I p l)
    (ET : Finset (Fin N × Fin N))
    (hET : ∀ e ∈ ET, Relation.ReflTransGen (stepR C (N + N)) e.1.val o ∧
      Relation.ReflTransGen (stepR C (N + N)) (N + e.2.val) o ∧
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)))).getD o false = true) :
    ET.card ≤ (ET.image Prod.fst).card + (ET.image Prod.snd).card := by
  classical
  let n := N + N
  let edge : Fin N → Fin N → Fin n → Bool := fun p l k =>
    decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
  let onlyP : Fin N → Fin n → Bool := fun p k => decide (k = Fin.castAdd N p)
  let onlyL : Fin N → Fin n → Bool := fun l k => decide (k = Fin.natAdd N l)
  let cone : ℕ → ℕ → Prop := fun w v => Relation.ReflTransGen (stepR C n) v w
  let orStep : ℕ → ℕ → Prop := fun a b =>
    ∃ j : Fin C.size, b = n + j.val ∧ (C.gates[j.val]'j.isLt).op = GateOp.or ∧
      a ∈ (C.gates[j.val]'j.isLt).inputs
  let orReach : ℕ → Prop := fun w => Relation.ReflTransGen orStep w o
  have hor_to_cone : ∀ w, orReach w → cone o w := by
    intro w hw
    induction hw using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | head hstep _ ih =>
      obtain ⟨j, rfl, _, hin⟩ := hstep
      exact Relation.ReflTransGen.head ⟨j, rfl, hin⟩ ih
  have hor_mono : ∀ w, orReach w → ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true →
      (C.wires (List.ofFn z)).getD o false = true := by
    intro w hw z hz
    induction hw using Relation.ReflTransGen.head_induction_on with
    | refl => exact hz
    | head hstep _ ih =>
      obtain ⟨j, rfl, hop, hin⟩ := hstep
      apply ih
      rw [isAO2_gate_eval hAO _ List.length_ofFn j.isLt, hop]
      simp only [gateOp_or_eval, List.any_eq_true, List.mem_map, id_eq]
      exact ⟨_, ⟨_, hin, rfl⟩, hz⟩
  have hcone_disj : ∀ w a b, cone o w → a < w → b < w → a ≠ b →
      stepR C n a w → stepR C n b w →
      ∀ v, ¬ (cone a v ∧ cone b v) := by
    intro w a b hwo haw hbw hab hsa hsb v ⟨hva, hvb⟩
    have hv_le : v ≤ w := (cone_le hAO hva).trans haw.le
    have hdisj_gen : ∀ d : ℕ, ∀ v, w - v = d → cone a v → cone b v → False := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro v hd hva hvb
        have hvo : cone o v := Relation.ReflTransGen.trans hva
          (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsa) hwo)
        by_cases hva_eq : v = a
        · subst hva_eq
          rcases Relation.ReflTransGen.cases_head hvb with rfl | ⟨u, ⟨j, hu, hin⟩, hub⟩
          · exact hab rfl
          · have hj_o : cone o (n + j.val) :=
              hu ▸ Relation.ReflTransGen.trans hub (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsb) hwo)
            have hle_b : n + j.val ≤ b := hu ▸ cone_le hAO hub
            obtain ⟨j₀, hw_eq, hin₀⟩ := hsa
            have ha_lt_j₀ : v < n + j₀.val := (ao2_gate_inputs hAO j₀.isLt).2.2 v hin₀
            have hwo_lt : n + j₀.val ≤ o := hw_eq ▸ cone_le hAO hwo
            have ha_lt_o : v < o := by omega
            have hmem0 := hin₀
            have hmem1 : v ∈ (C.gates[j.val]'j.isLt).inputs := hin
            obtain ⟨c0, hc0⟩ : ∃ c0 : Fin 2, (C.gates[j₀.val]'j₀.isLt).inputs.getD c0.val 0 = v := by
              obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₀.isLt).2.1
              have hmem0' : v ∈ (C.gates[j₀.val]'j₀.isLt).inputs := hmem0
              rw [hx] at hmem0'
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem0'
              rcases hmem0' with rfl | rfl
              · exact ⟨0, by change (C.gates[j₀.val]'j₀.isLt).inputs.getD 0 0 = v; rw [hx]; rfl⟩
              · exact ⟨1, by change (C.gates[j₀.val]'j₀.isLt).inputs.getD 1 0 = v; rw [hx]; rfl⟩
            obtain ⟨c1, hc1⟩ : ∃ c1 : Fin 2, (C.gates[j.val]'j.isLt).inputs.getD c1.val 0 = v := by
              obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j.isLt).2.1
              have hmem1' : v ∈ (C.gates[j.val]'j.isLt).inputs := hmem1
              rw [hx] at hmem1'
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem1'
              rcases hmem1' with rfl | rfl
              · exact ⟨0, by change (C.gates[j.val]'j.isLt).inputs.getD 0 0 = v; rw [hx]; rfl⟩
              · exact ⟨1, by change (C.gates[j.val]'j.isLt).inputs.getD 1 0 = v; rw [hx]; rfl⟩
            have heq := (huniq_read v ha_lt_o hvo j₀ j c0 c1 (hw_eq ▸ hwo) hj_o hc0 hc1).1
            rw [← heq] at hle_b
            omega
        · rcases Relation.ReflTransGen.cases_head hva with rfl | ⟨u₁, ⟨j₁, hu₁, hin₁⟩, hua⟩
          · exact hva_eq rfl
          · rcases Relation.ReflTransGen.cases_head hvb with rfl | ⟨u₂, ⟨j₂, hu₂, hin₂⟩, hvb'⟩
            · have hj_o : cone o (n + j₁.val) :=
                hu₁ ▸ Relation.ReflTransGen.trans hua (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsa) hwo)
              have hle_a : n + j₁.val ≤ a := hu₁ ▸ cone_le hAO hua
              obtain ⟨j₀, hw_eq, hin₀⟩ := hsb
              have hb_lt_j₀ : v < n + j₀.val := (ao2_gate_inputs hAO j₀.isLt).2.2 v hin₀
              have hwo_lt : n + j₀.val ≤ o := hw_eq ▸ cone_le hAO hwo
              have hb_lt_o : v < o := by omega
              have hmem0 := hin₀
              have hmem1 : v ∈ (C.gates[j₁.val]'j₁.isLt).inputs := hin₁
              obtain ⟨c0, hc0⟩ : ∃ c0 : Fin 2, (C.gates[j₀.val]'j₀.isLt).inputs.getD c0.val 0 = v := by
                obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₀.isLt).2.1
                have hmem0' : v ∈ (C.gates[j₀.val]'j₀.isLt).inputs := hmem0
                rw [hx] at hmem0'
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem0'
                rcases hmem0' with rfl | rfl
                · exact ⟨0, by change (C.gates[j₀.val]'j₀.isLt).inputs.getD 0 0 = v; rw [hx]; rfl⟩
                · exact ⟨1, by change (C.gates[j₀.val]'j₀.isLt).inputs.getD 1 0 = v; rw [hx]; rfl⟩
              obtain ⟨c1, hc1⟩ : ∃ c1 : Fin 2, (C.gates[j₁.val]'j₁.isLt).inputs.getD c1.val 0 = v := by
                obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₁.isLt).2.1
                have hmem1' : v ∈ (C.gates[j₁.val]'j₁.isLt).inputs := hmem1
                rw [hx] at hmem1'
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem1'
                rcases hmem1' with rfl | rfl
                · exact ⟨0, by change (C.gates[j₁.val]'j₁.isLt).inputs.getD 0 0 = v; rw [hx]; rfl⟩
                · exact ⟨1, by change (C.gates[j₁.val]'j₁.isLt).inputs.getD 1 0 = v; rw [hx]; rfl⟩
              have heq := (huniq_read v hb_lt_o hvo j₀ j₁ c0 c1 (hw_eq ▸ hwo) hj_o hc0 hc1).1
              rw [← heq] at hle_a
              omega
            · have hle_w : w ≤ o := cone_le hAO hwo
              have hv_lt_j1 : v < n + j₁.val := (ao2_gate_inputs hAO j₁.isLt).2.2 v hin₁
              have hle_a : n + j₁.val ≤ a := hu₁ ▸ cone_le hAO hua
              have hv_lt_o : v < o := by omega
              have hj1_o : cone o (n + j₁.val) :=
                hu₁ ▸ Relation.ReflTransGen.trans hua (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsa) hwo)
              have hj2_o : cone o (n + j₂.val) :=
                hu₂ ▸ Relation.ReflTransGen.trans hvb' (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsb) hwo)
              obtain ⟨c1, hc1⟩ : ∃ c1 : Fin 2, (C.gates[j₁.val]'j₁.isLt).inputs.getD c1.val 0 = v := by
                obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₁.isLt).2.1
                have hmem1 : v ∈ (C.gates[j₁.val]'j₁.isLt).inputs := hin₁
                rw [hx] at hmem1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem1
                rcases hmem1 with rfl | rfl
                · exact ⟨0, by change (C.gates[j₁.val]'j₁.isLt).inputs.getD 0 0 = v; rw [hx]; rfl⟩
                · exact ⟨1, by change (C.gates[j₁.val]'j₁.isLt).inputs.getD 1 0 = v; rw [hx]; rfl⟩
              obtain ⟨c2, hc2⟩ : ∃ c2 : Fin 2, (C.gates[j₂.val]'j₂.isLt).inputs.getD c2.val 0 = v := by
                obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₂.isLt).2.1
                have hmem2 : v ∈ (C.gates[j₂.val]'j₂.isLt).inputs := hin₂
                rw [hx] at hmem2
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
                rcases hmem2 with rfl | rfl
                · exact ⟨0, by change (C.gates[j₂.val]'j₂.isLt).inputs.getD 0 0 = v; rw [hx]; rfl⟩
                · exact ⟨1, by change (C.gates[j₂.val]'j₂.isLt).inputs.getD 1 0 = v; rw [hx]; rfl⟩
              have hj_eq := (huniq_read v hv_lt_o hvo j₁ j₂ c1 c2 hj1_o hj2_o hc1 hc2).1
              have hu_eq : u₁ = u₂ := by rw [hu₁, hu₂, hj_eq]
              have hv_lt_u : v < u₁ := by omega
              have hu_le_w : u₁ ≤ w := by omega
              exact ih (w - u₁) (by omega) u₁ rfl hua (hu_eq ▸ hvb')
    exact hdisj_gen (w - v) v rfl hva hvb
  have hmain : ∀ w, orReach w →
      (ET.filter fun e => cone w e.1.val ∧ cone w (N + e.2.val) ∧
        (C.wires (List.ofFn (edge e.1 e.2))).getD w false = true).card ≤
      ((ET.image Prod.fst).filter fun p => cone w p.val).card +
      ((ET.image Prod.snd).filter fun l => cone w (N + l.val)).card := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw_or
      have hw_cone : cone o w := hor_to_cone w hw_or
      have hw_p : ∀ p : Fin N, (C.wires (List.ofFn (onlyP p))).getD w false = false := by
        intro p
        cases hval : (C.wires (List.ofFn (onlyP p))).getD w false
        · rfl
        · have ho := hor_mono w hw_or (onlyP p) hval
          rw [hsound_p p] at ho
          cases ho
      have hw_l : ∀ l : Fin N, (C.wires (List.ofFn (onlyL l))).getD w false = false := by
        intro l
        cases hval : (C.wires (List.ofFn (onlyL l))).getD w false
        · rfl
        · have ho := hor_mono w hw_or (onlyL l) hval
          rw [hsound_l l] at ho
          cases ho
      by_cases hlt : w < n
      · have hemp : ET.filter (fun e => cone w e.1.val ∧ cone w (N + e.2.val) ∧
            (C.wires (List.ofFn (edge e.1 e.2))).getD w false = true) = ∅ := by
          ext e
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _ _ _ hval
          rw [wires_eq_runW] at hval
          have hpr := runW_prefix_getD [] C.gates (List.ofFn (edge e.1 e.2)) w (by simp; omega)
          rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil] at hval
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some,
            edge, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hval
          rcases hval with h1 | h2
          · have hp := hw_p e.1
            rw [wires_eq_runW, show C.gates = [] ++ C.gates from rfl,
                runW_prefix_getD [] C.gates (List.ofFn (onlyP e.1)) w (by simp; omega), runW_nil] at hp
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some,
              onlyP, decide_eq_false_iff_not, Fin.ext_iff, Fin.val_castAdd] at hp
            exact hp h1
          · have hl := hw_l e.2
            rw [wires_eq_runW, show C.gates = [] ++ C.gates from rfl,
                runW_prefix_getD [] C.gates (List.ofFn (onlyL e.2)) w (by simp; omega), runW_nil] at hl
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some,
              onlyL, decide_eq_false_iff_not, Fin.ext_iff, Fin.val_natAdd] at hl
            exact hl h2
        rw [hemp]
        simp
      · have hltg : w < n + C.gates.length := by
          have := cone_le hAO hw_cone
          omega
        let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        have hk' : k < C.size := hk
        obtain ⟨hop, hlen, hrb⟩ := ao2_gate_inputs hAO hk
        obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
        have ha_lt : a < w := by rw [hwk]; exact hrb a (by rw [hab]; simp)
        have hb_lt : b < w := by rw [hwk]; exact hrb b (by rw [hab]; simp)
        have hsa : stepR C n a w := ⟨⟨k, hk'⟩, hwk, by change a ∈ (C.gates[k]'hk).inputs; rw [hab]; simp⟩
        have hsb : stepR C n b w := ⟨⟨k, hk'⟩, hwk, by change b ∈ (C.gates[k]'hk).inputs; rw [hab]; simp⟩
        have hab_ne : a ≠ b := by
          intro heq
          subst heq
          have hle_o : w ≤ o := cone_le hAO hw_cone
          have ha_lt_o : a < o := by omega
          have ha_o : cone o a := Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsa) hw_cone
          have h01 := (huniq_read a ha_lt_o ha_o ⟨k, hk'⟩ ⟨k, hk'⟩ 0 1 (hwk ▸ hw_cone) (hwk ▸ hw_cone)
            (by change (C.gates[k]'hk).inputs.getD 0 0 = a; rw [hab]; rfl)
            (by change (C.gates[k]'hk).inputs.getD 1 0 = a; rw [hab]; rfl)).2
          cases h01
        have hdisj_ab := hcone_disj w a b hw_cone ha_lt hb_lt hab_ne hsa hsb
        have hcone_split : ∀ v, v < n → cone w v → cone a v ∨ cone b v := by
          intro v hv hvw
          rcases Relation.ReflTransGen.cases_tail hvw with rfl | ⟨u, hvu, hstep⟩
          · omega
          · obtain ⟨j, hj, hin⟩ := hstep
            rw [hwk] at hj
            have hj_eq : j = ⟨k, hk'⟩ := Fin.ext (Nat.add_left_cancel hj.symm)
            rw [hj_eq] at hin
            change u ∈ (C.gates[k]'hk).inputs at hin
            rw [hab] at hin
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
            rcases hin with rfl | rfl
            · exact Or.inl hvu
            · exact Or.inr hvu
        rcases hop with hop_and | hop_or
        · -- AND gate case
          let Pa := (ET.image Prod.fst).filter fun p =>
            cone a p.val ∧ (C.wires (List.ofFn (onlyP p))).getD a false = true
          let Pb := (ET.image Prod.fst).filter fun p =>
            cone b p.val ∧ (C.wires (List.ofFn (onlyP p))).getD b false = true
          let La := (ET.image Prod.snd).filter fun l =>
            cone a (N + l.val) ∧ (C.wires (List.ofFn (onlyL l))).getD a false = true
          let Lb := (ET.image Prod.snd).filter fun l =>
            cone b (N + l.val) ∧ (C.wires (List.ofFn (onlyL l))).getD b false = true
          have hI_ab : ∀ p ∈ Pa, ∀ l ∈ Lb, I p l := by
            intro p hp l hl
            have hpa := (Finset.mem_filter.mp hp).2
            have hlb := (Finset.mem_filter.mp hl).2
            have ha_t : (C.wires (List.ofFn (edge p l))).getD a false = true :=
              wires_mono_of_isAO2 hAO (onlyP p) (edge p l)
                (fun i hi => by simp only [onlyP, decide_eq_true_eq] at hi; simp [edge, hi]) a hpa.2
            have hb_t : (C.wires (List.ofFn (edge p l))).getD b false = true :=
              wires_mono_of_isAO2 hAO (onlyL l) (edge p l)
                (fun i hi => by simp only [onlyL, decide_eq_true_eq] at hi; simp [edge, hi]) b hlb.2
            have hw_t : (C.wires (List.ofFn (edge p l))).getD w false = true := by
              rw [hwk, isAO2_gate_eval hAO _ List.length_ofFn hk, hab, hop_and]
              simp only [gateOp_and_eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, ha_t, hb_t, Bool.and_self]
            have ho_t := hor_mono w hw_or (edge p l) hw_t
            exact hsound_edge p l
              (Relation.ReflTransGen.trans hpa.1 (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsa) hw_cone))
              (Relation.ReflTransGen.trans hlb.1 (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsb) hw_cone))
              ho_t
          have hI_ba : ∀ p ∈ Pb, ∀ l ∈ La, I p l := by
            intro p hp l hl
            have hpb := (Finset.mem_filter.mp hp).2
            have hla := (Finset.mem_filter.mp hl).2
            have ha_t : (C.wires (List.ofFn (edge p l))).getD a false = true :=
              wires_mono_of_isAO2 hAO (onlyL l) (edge p l)
                (fun i hi => by simp only [onlyL, decide_eq_true_eq] at hi; simp [edge, hi]) a hla.2
            have hb_t : (C.wires (List.ofFn (edge p l))).getD b false = true :=
              wires_mono_of_isAO2 hAO (onlyP p) (edge p l)
                (fun i hi => by simp only [onlyP, decide_eq_true_eq] at hi; simp [edge, hi]) b hpb.2
            have hw_t : (C.wires (List.ofFn (edge p l))).getD w false = true := by
              rw [hwk, isAO2_gate_eval hAO _ List.length_ofFn hk, hab, hop_and]
              simp only [gateOp_and_eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, ha_t, hb_t, Bool.and_self]
            have ho_t := hor_mono w hw_or (edge p l) hw_t
            exact hsound_edge p l
              (Relation.ReflTransGen.trans hpb.1 (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsb) hw_cone))
              (Relation.ReflTransGen.trans hla.1 (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hsa) hw_cone))
              ho_t
          have hcard_ab : (Pa ×ˢ Lb).card ≤ Pa.card + Lb.card := by
            rw [Finset.card_product]
            by_cases hpa : Pa.card ≤ 1
            · calc Pa.card * Lb.card ≤ 1 * Lb.card := Nat.mul_le_mul_right _ hpa
                _ ≤ Pa.card + Lb.card := by omega
            · have hlb : Lb.card ≤ 1 := by
                by_contra hlb'
                push Not at hpa hlb'
                obtain ⟨p₁, hp₁, p₂, hp₂, hpp⟩ := Finset.one_lt_card.mp hpa
                obtain ⟨l₁, hl₁, l₂, hl₂, hll⟩ := Finset.one_lt_card.mp hlb'
                exact hfour p₁ p₂ l₁ l₂ hpp hll ⟨hI_ab p₁ hp₁ l₁ hl₁, hI_ab p₂ hp₂ l₁ hl₁,
                  hI_ab p₁ hp₁ l₂ hl₂, hI_ab p₂ hp₂ l₂ hl₂⟩
              calc Pa.card * Lb.card ≤ Pa.card * 1 := Nat.mul_le_mul_left _ hlb
                _ ≤ Pa.card + Lb.card := by omega
          have hcard_ba : (Pb ×ˢ La).card ≤ Pb.card + La.card := by
            rw [Finset.card_product]
            by_cases hpb : Pb.card ≤ 1
            · calc Pb.card * La.card ≤ 1 * La.card := Nat.mul_le_mul_right _ hpb
                _ ≤ Pb.card + La.card := by omega
            · have hla : La.card ≤ 1 := by
                by_contra hla'
                push Not at hpb hla'
                obtain ⟨p₁, hp₁, p₂, hp₂, hpp⟩ := Finset.one_lt_card.mp hpb
                obtain ⟨l₁, hl₁, l₂, hl₂, hll⟩ := Finset.one_lt_card.mp hla'
                exact hfour p₁ p₂ l₁ l₂ hpp hll ⟨hI_ba p₁ hp₁ l₁ hl₁, hI_ba p₂ hp₂ l₁ hl₁,
                  hI_ba p₁ hp₁ l₂ hl₂, hI_ba p₂ hp₂ l₂ hl₂⟩
              calc Pb.card * La.card ≤ Pb.card * 1 := Nat.mul_le_mul_left _ hla
                _ ≤ Pb.card + La.card := by omega
          have hsub_ew : ET.filter (fun e => cone w e.1.val ∧ cone w (N + e.2.val) ∧
              (C.wires (List.ofFn (edge e.1 e.2))).getD w false = true) ⊆ (Pa ×ˢ Lb) ∪ (Pb ×ˢ La) := by
            intro e he
            obtain ⟨heET, hcp, hcl, hwt⟩ := Finset.mem_filter.mp he
            rw [hwk, isAO2_gate_eval hAO _ List.length_ofFn hk, hab, hop_and] at hwt
            simp only [gateOp_and_eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hwt
            obtain ⟨hat, hbt⟩ := hwt
            have hcp' := hcone_split e.1.val (by have := e.1.isLt; omega) hcp
            have hcl' := hcone_split (N + e.2.val) (by have := e.2.isLt; omega) hcl
            rcases hcp' with hpa | hpb <;> rcases hcl' with hla | hlb
            · exfalso
              have hnone_p : ¬ cone b e.1.val := fun h => hdisj_ab e.1.val ⟨hpa, h⟩
              have hnone_l : ¬ cone b (N + e.2.val) := fun h => hdisj_ab (N + e.2.val) ⟨hla, h⟩
              have heq0 : (C.wires (List.ofFn (edge e.1 e.2))).getD b false =
                  (C.wires (List.ofFn (fun _ : Fin n => false))).getD b false := by
                apply eval_eq_of_cone hAO b _ _ _ b Relation.ReflTransGen.refl
                intro i hi
                simp only [edge, decide_eq_false_iff_not, not_or]
                exact ⟨fun h => hnone_p (by have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; simpa [hv] using hi),
                       fun h => hnone_l (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hi)⟩
              have hrep : List.ofFn (fun _ : Fin n => false) = List.replicate n false := List.ofFn_const _ _
              rw [heq0, hrep, isAO2_w0_false hAO b] at hbt
              cases hbt
            · refine Finset.mem_union_left _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
              · refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ heET, hpa, ?_⟩
                rw [← hat]
                apply eval_eq_of_cone hAO a _ _ _ a Relation.ReflTransGen.refl
                intro i hi
                by_cases h1 : i = Fin.castAdd N e.1
                · simp [onlyP, edge, h1]
                · have h2 : i ≠ Fin.natAdd N e.2 := by
                    intro heq
                    have hv := congrArg Fin.val heq
                    simp only [Fin.val_natAdd] at hv
                    exact hdisj_ab (N + e.2.val) ⟨by simpa [hv, Nat.add_comm] using hi, hlb⟩
                  simp only [onlyP, edge, h1, h2, or_false]
              · refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ heET, hlb, ?_⟩
                rw [← hbt]
                apply eval_eq_of_cone hAO b _ _ _ b Relation.ReflTransGen.refl
                intro i hi
                by_cases h2 : i = Fin.natAdd N e.2
                · simp [onlyL, edge, h2]
                · have h1 : i ≠ Fin.castAdd N e.1 := by
                    intro heq
                    have hv := congrArg Fin.val heq
                    simp only [Fin.val_castAdd] at hv
                    exact hdisj_ab e.1.val ⟨hpa, by simpa [hv] using hi⟩
                  simp only [onlyL, edge, h1, h2, false_or]
            · refine Finset.mem_union_right _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
              · refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ heET, hpb, ?_⟩
                rw [← hbt]
                apply eval_eq_of_cone hAO b _ _ _ b Relation.ReflTransGen.refl
                intro i hi
                by_cases h1 : i = Fin.castAdd N e.1
                · simp [onlyP, edge, h1]
                · have h2 : i ≠ Fin.natAdd N e.2 := by
                    intro heq
                    have hv := congrArg Fin.val heq
                    simp only [Fin.val_natAdd] at hv
                    exact hdisj_ab (N + e.2.val) ⟨hla, by simpa [hv, Nat.add_comm] using hi⟩
                  simp only [onlyP, edge, h1, h2, or_false]
              · refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ heET, hla, ?_⟩
                rw [← hat]
                apply eval_eq_of_cone hAO a _ _ _ a Relation.ReflTransGen.refl
                intro i hi
                by_cases h2 : i = Fin.natAdd N e.2
                · simp [onlyL, edge, h2]
                · have h1 : i ≠ Fin.castAdd N e.1 := by
                    intro heq
                    have hv := congrArg Fin.val heq
                    simp only [Fin.val_castAdd] at hv
                    exact hdisj_ab e.1.val ⟨by simpa [hv] using hi, hpb⟩
                  simp only [onlyL, edge, h1, h2, false_or]
            · exfalso
              have hnone_p : ¬ cone a e.1.val := fun h => hdisj_ab e.1.val ⟨h, hpb⟩
              have hnone_l : ¬ cone a (N + e.2.val) := fun h => hdisj_ab (N + e.2.val) ⟨h, hlb⟩
              have heq0 : (C.wires (List.ofFn (edge e.1 e.2))).getD a false =
                  (C.wires (List.ofFn (fun _ : Fin n => false))).getD a false := by
                apply eval_eq_of_cone hAO a _ _ _ a Relation.ReflTransGen.refl
                intro i hi
                simp only [edge, decide_eq_false_iff_not, not_or]
                exact ⟨fun h => hnone_p (by have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; simpa [hv] using hi),
                       fun h => hnone_l (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hi)⟩
              have hrep : List.ofFn (fun _ : Fin n => false) = List.replicate n false := List.ofFn_const _ _
              rw [heq0, hrep, isAO2_w0_false hAO a] at hat
              cases hat
          have hPaPb_disj : Disjoint Pa Pb := by
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            exact hdisj_ab p.val ⟨(Finset.mem_filter.mp hp1).2.1, (Finset.mem_filter.mp hp2).2.1⟩
          have hLaLb_disj : Disjoint La Lb := by
            rw [Finset.disjoint_left]
            intro l hl1 hl2
            exact hdisj_ab (N + l.val) ⟨(Finset.mem_filter.mp hl1).2.1, (Finset.mem_filter.mp hl2).2.1⟩
          have hP_sub : Pa ∪ Pb ⊆ (ET.image Prod.fst).filter fun p => cone w p.val := by
            intro p hp
            rcases Finset.mem_union.mp hp with hp | hp <;> obtain ⟨hmem, hc, _⟩ := Finset.mem_filter.mp hp
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsa)⟩
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsb)⟩
          have hL_sub : La ∪ Lb ⊆ (ET.image Prod.snd).filter fun l => cone w (N + l.val) := by
            intro l hl
            rcases Finset.mem_union.mp hl with hl | hl <;> obtain ⟨hmem, hc, _⟩ := Finset.mem_filter.mp hl
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsa)⟩
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsb)⟩
          have hP_le : Pa.card + Pb.card ≤ ((ET.image Prod.fst).filter fun p => cone w p.val).card := by
            rw [← Finset.card_union_of_disjoint hPaPb_disj]
            exact Finset.card_le_card hP_sub
          have hL_le : La.card + Lb.card ≤ ((ET.image Prod.snd).filter fun l => cone w (N + l.val)).card := by
            rw [← Finset.card_union_of_disjoint hLaLb_disj]
            exact Finset.card_le_card hL_sub
          calc (ET.filter _).card ≤ ((Pa ×ˢ Lb) ∪ (Pb ×ˢ La)).card := Finset.card_le_card hsub_ew
            _ ≤ (Pa ×ˢ Lb).card + (Pb ×ˢ La).card := Finset.card_union_le _ _
            _ ≤ (Pa.card + Lb.card) + (Pb.card + La.card) := Nat.add_le_add hcard_ab hcard_ba
            _ ≤ ((ET.image Prod.fst).filter _).card + ((ET.image Prod.snd).filter _).card := by omega
        · -- OR gate case
          have ha_or : orReach a := Relation.ReflTransGen.head
            ⟨⟨k, hk'⟩, hwk, hop_or, by change a ∈ (C.gates[k]'hk).inputs; rw [hab]; simp⟩ hw_or
          have hb_or : orReach b := Relation.ReflTransGen.head
            ⟨⟨k, hk'⟩, hwk, hop_or, by change b ∈ (C.gates[k]'hk).inputs; rw [hab]; simp⟩ hw_or
          have iha := ih a ha_lt ha_or
          have ihb := ih b hb_lt hb_or
          let Ea := ET.filter fun e => cone a e.1.val ∧ cone a (N + e.2.val) ∧
            (C.wires (List.ofFn (edge e.1 e.2))).getD a false = true
          let Eb := ET.filter fun e => cone b e.1.val ∧ cone b (N + e.2.val) ∧
            (C.wires (List.ofFn (edge e.1 e.2))).getD b false = true
          have hsub_ew : ET.filter (fun e => cone w e.1.val ∧ cone w (N + e.2.val) ∧
              (C.wires (List.ofFn (edge e.1 e.2))).getD w false = true) ⊆ Ea ∪ Eb := by
            intro e he
            obtain ⟨heET, hcp, hcl, hwt⟩ := Finset.mem_filter.mp he
            rw [hwk, isAO2_gate_eval hAO _ List.length_ofFn hk, hab, hop_or] at hwt
            simp only [gateOp_or_eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true] at hwt
            rcases hwt with hat | hbt
            · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heET, ?_, ?_, hat⟩)
              · by_contra hna
                have heq : (C.wires (List.ofFn (edge e.1 e.2))).getD a false =
                    (C.wires (List.ofFn (onlyL e.2))).getD a false := by
                  apply eval_eq_of_cone hAO a _ _ _ a Relation.ReflTransGen.refl
                  intro i hi
                  have hne : i ≠ Fin.castAdd N e.1 := by
                    intro heq'; have hv := congrArg Fin.val heq'; simp at hv
                    exact hna (by simpa [hv] using hi)
                  simp only [edge, onlyL, hne, false_or]
                have hla := hor_mono a ha_or (onlyL e.2) (heq ▸ hat)
                rw [hsound_l e.2] at hla; cases hla
              · by_contra hnl
                have heq : (C.wires (List.ofFn (edge e.1 e.2))).getD a false =
                    (C.wires (List.ofFn (onlyP e.1))).getD a false := by
                  apply eval_eq_of_cone hAO a _ _ _ a Relation.ReflTransGen.refl
                  intro i hi
                  have hne : i ≠ Fin.natAdd N e.2 := by
                    intro heq'; have hv := congrArg Fin.val heq'; simp at hv
                    exact hnl (by simpa [hv, Nat.add_comm] using hi)
                  simp only [edge, onlyP, hne, or_false]
                have hpa := hor_mono a ha_or (onlyP e.1) (heq ▸ hat)
                rw [hsound_p e.1] at hpa; cases hpa
            · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heET, ?_, ?_, hbt⟩)
              · by_contra hnb
                have heq : (C.wires (List.ofFn (edge e.1 e.2))).getD b false =
                    (C.wires (List.ofFn (onlyL e.2))).getD b false := by
                  apply eval_eq_of_cone hAO b _ _ _ b Relation.ReflTransGen.refl
                  intro i hi
                  have hne : i ≠ Fin.castAdd N e.1 := by
                    intro heq'; have hv := congrArg Fin.val heq'; simp at hv
                    exact hnb (by simpa [hv] using hi)
                  simp only [edge, onlyL, hne, false_or]
                have hlb := hor_mono b hb_or (onlyL e.2) (heq ▸ hbt)
                rw [hsound_l e.2] at hlb; cases hlb
              · by_contra hnl
                have heq : (C.wires (List.ofFn (edge e.1 e.2))).getD b false =
                    (C.wires (List.ofFn (onlyP e.1))).getD b false := by
                  apply eval_eq_of_cone hAO b _ _ _ b Relation.ReflTransGen.refl
                  intro i hi
                  have hne : i ≠ Fin.natAdd N e.2 := by
                    intro heq'; have hv := congrArg Fin.val heq'; simp at hv
                    exact hnl (by simpa [hv, Nat.add_comm] using hi)
                  simp only [edge, onlyP, hne, or_false]
                have hpb := hor_mono b hb_or (onlyP e.1) (heq ▸ hbt)
                rw [hsound_p e.1] at hpb; cases hpb
          have hP_disj : Disjoint ((ET.image Prod.fst).filter fun p => cone a p.val)
              ((ET.image Prod.fst).filter fun p => cone b p.val) := by
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            exact hdisj_ab p.val ⟨(Finset.mem_filter.mp hp1).2, (Finset.mem_filter.mp hp2).2⟩
          have hL_disj : Disjoint ((ET.image Prod.snd).filter fun l => cone a (N + l.val))
              ((ET.image Prod.snd).filter fun l => cone b (N + l.val)) := by
            rw [Finset.disjoint_left]
            intro l hl1 hl2
            exact hdisj_ab (N + l.val) ⟨(Finset.mem_filter.mp hl1).2, (Finset.mem_filter.mp hl2).2⟩
          have hP_sub : ((ET.image Prod.fst).filter fun p => cone a p.val) ∪
              ((ET.image Prod.fst).filter fun p => cone b p.val) ⊆
              (ET.image Prod.fst).filter fun p => cone w p.val := by
            intro p hp
            rcases Finset.mem_union.mp hp with hp | hp <;> obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hp
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsa)⟩
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsb)⟩
          have hL_sub : ((ET.image Prod.snd).filter fun l => cone a (N + l.val)) ∪
              ((ET.image Prod.snd).filter fun l => cone b (N + l.val)) ⊆
              (ET.image Prod.snd).filter fun l => cone w (N + l.val) := by
            intro l hl
            rcases Finset.mem_union.mp hl with hl | hl <;> obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hl
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsa)⟩
            · exact Finset.mem_filter.mpr ⟨hmem, Relation.ReflTransGen.trans hc (Relation.ReflTransGen.single hsb)⟩
          have hP_le : ((ET.image Prod.fst).filter fun p => cone a p.val).card +
              ((ET.image Prod.fst).filter fun p => cone b p.val).card ≤
              ((ET.image Prod.fst).filter fun p => cone w p.val).card := by
            rw [← Finset.card_union_of_disjoint hP_disj]
            exact Finset.card_le_card hP_sub
          have hL_le : ((ET.image Prod.snd).filter fun l => cone a (N + l.val)).card +
              ((ET.image Prod.snd).filter fun l => cone b (N + l.val)).card ≤
              ((ET.image Prod.snd).filter fun l => cone w (N + l.val)).card := by
            rw [← Finset.card_union_of_disjoint hL_disj]
            exact Finset.card_le_card hL_sub
          have hle_res : (ET.filter fun e => cone w e.1.val ∧ cone w (N + e.2.val) ∧
              (C.wires (List.ofFn (edge e.1 e.2))).getD w false = true).card ≤
              ((ET.image Prod.fst).filter fun p => cone w p.val).card +
              ((ET.image Prod.snd).filter fun l => cone w (N + l.val)).card := by
            have h1 := Finset.card_le_card hsub_ew
            have h2 := Finset.card_union_le Ea Eb
            have ha_le : Ea.card ≤ ((ET.image Prod.fst).filter fun p => cone a p.val).card +
                ((ET.image Prod.snd).filter fun l => cone a (N + l.val)).card := iha
            have hb_le : Eb.card ≤ ((ET.image Prod.fst).filter fun p => cone b p.val).card +
                ((ET.image Prod.snd).filter fun l => cone b (N + l.val)).card := ihb
            omega
          exact hle_res
  have htop := hmain o Relation.ReflTransGen.refl
  have heq1 : ET.filter (fun e => cone o e.1.val ∧ cone o (N + e.2.val) ∧
      (C.wires (List.ofFn (edge e.1 e.2))).getD o false = true) = ET := by
    ext e
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro he
    exact hET e he
  have hsub_p : (ET.image Prod.fst).filter (fun p => cone o p.val) ⊆ ET.image Prod.fst := Finset.filter_subset _ _
  have hsub_l : (ET.image Prod.snd).filter (fun l => cone o (N + l.val)) ⊆ ET.image Prod.snd := Finset.filter_subset _ _
  rw [heq1] at htop
  exact htop.trans (Nat.add_le_add (Finset.card_le_card hsub_p) (Finset.card_le_card hsub_l))

private def forcedInit (n w₀ : ℕ) (b₀ : Bool) (z : Fin n → Bool) : List Bool :=
  (List.finRange n).map fun i => if i.val = w₀ then b₀ else z i

private lemma forcedInit_len (n w₀ : ℕ) (b₀ : Bool) (z : Fin n → Bool) :
    (forcedInit n w₀ b₀ z).length = n := by
  simp [forcedInit]

private def runForced (n w₀ : ℕ) (b₀ : Bool) (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g =>
    let v := if w.length = w₀ then b₀ else g.op.eval (g.inputs.map fun i => w.getD i false)
    w ++ [v]) x

private lemma runForced_nil (n w₀ : ℕ) (b₀ : Bool) (x : List Bool) :
    runForced n w₀ b₀ [] x = x := rfl

private lemma runForced_snoc (n w₀ : ℕ) (b₀ : Bool) (gs : List Gate) (g : Gate) (x : List Bool) :
    runForced n w₀ b₀ (gs ++ [g]) x =
      runForced n w₀ b₀ gs x ++
        [if (runForced n w₀ b₀ gs x).length = w₀ then b₀
         else g.op.eval (g.inputs.map fun i => (runForced n w₀ b₀ gs x).getD i false)] := by
  simp [runForced]

private lemma runForced_len (n w₀ : ℕ) (b₀ : Bool) (gs : List Gate) (x : List Bool) :
    (runForced n w₀ b₀ gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runForced]
  | append_singleton gs g ih => simp [runForced_snoc, ih]; omega

private lemma runForced_prefix_getD (n w₀ : ℕ) (b₀ : Bool) (g1 g2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + g1.length) :
    (runForced n w₀ b₀ (g1 ++ g2) x).getD i false = (runForced n w₀ b₀ g1 x).getD i false := by
  induction g2 using List.reverseRecOn with
  | nil => simp
  | append_singleton g2 g ih =>
    rw [← List.append_assoc, runForced_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left]
    · rw [← List.getD_eq_getElem?_getD]
      exact ih
    · rw [runForced_len, List.length_append]
      omega

private lemma runForced_gate_getD (n w₀ : ℕ) (b₀ : Bool) (gs : List Gate) (x : List Bool)
    (k : ℕ) (hk : k < gs.length) :
    (runForced n w₀ b₀ gs x).getD (x.length + k) false =
      if x.length + k = w₀ then b₀
      else (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (runForced n w₀ b₀ (gs.take k) x).getD i false) := by
  have hsplit : gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  conv_lhs => rw [hsplit]
  have hlenk : (gs.take k).length = k := List.length_take_of_le hk.le
  rw [runForced_prefix_getD n w₀ b₀ (gs.take k ++ [gs[k]'hk]) (gs.drop (k + 1)) x (x.length + k)
    (by simp; omega)]
  rw [runForced_snoc]
  have hlenw : (runForced n w₀ b₀ (gs.take k) x).length = x.length + k := by rw [runForced_len, hlenk]
  rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
  simp [hlenw]

private def evalForcedW (C : Circuit) (n w₀ : ℕ) (b₀ : Bool) (z : Fin n → Bool) : List Bool :=
  runForced n w₀ b₀ C.gates (forcedInit n w₀ b₀ z)

private lemma evalForcedW_input {n : ℕ} (C : Circuit) (w₀ : ℕ) (b₀ : Bool) (z : Fin n → Bool)
    {w : ℕ} (hw : w < n) :
    (evalForcedW C n w₀ b₀ z).getD w false = if w = w₀ then b₀ else z ⟨w, hw⟩ := by
  rw [evalForcedW]
  have hpr := runForced_prefix_getD n w₀ b₀ [] C.gates (forcedInit n w₀ b₀ z) w
    (by simp [forcedInit_len]; exact hw)
  rw [show C.gates = [] ++ C.gates from rfl, hpr, runForced_nil]
  simp [forcedInit, List.getD_eq_getElem?_getD, hw]

private lemma evalForcedW_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w₀ : ℕ) (b₀ : Bool)
    (z : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length) :
    (evalForcedW C n w₀ b₀ z).getD (n + k) false =
      if n + k = w₀ then b₀
      else (C.gates[k]'hk).op.eval
        ((C.gates[k]'hk).inputs.map fun i => (evalForcedW C n w₀ b₀ z).getD i false) := by
  rw [evalForcedW]
  have h := runForced_gate_getD n w₀ b₀ C.gates (forcedInit n w₀ b₀ z) k hk
  rw [forcedInit_len] at h
  rw [h]
  split_ifs with heq
  · rfl
  · congr 1
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < n + k := (ao2_gate_inputs hAO hk).2.2 i hi
    have hlenk : (C.gates.take k).length = k := List.length_take_of_le hk.le
    have hpr := runForced_prefix_getD n w₀ b₀ (C.gates.take k) (C.gates.drop k)
      (forcedInit n w₀ b₀ z) i (by rw [forcedInit_len, hlenk]; exact hi_lt)
    rw [List.take_append_drop] at hpr
    exact hpr.symm

private lemma evalForcedW_false_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w₀ : ℕ)
    (z : Fin n → Bool) :
    ∀ w, (evalForcedW C n w₀ false z).getD w false = true →
      (C.wires (List.ofFn z)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [evalForcedW_input C w₀ false z hlt] at hw
      split_ifs at hw with heq
      rw [wires_eq_runW]
      have hpr := runW_prefix_getD [] C.gates (List.ofFn z) w (by simp; omega)
      rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some, hw]
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        rw [hwk, evalForcedW_gate hAO w₀ false z hk] at hw
        split_ifs at hw with heq
        rw [hwk, isAO2_gate_eval hAO _ List.length_ofFn hk]
        obtain ⟨hop, hlen, hrb⟩ := ao2_gate_inputs hAO hk
        obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
        change (C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => (evalForcedW C n w₀ false z).getD i false) = true at hw
        rw [hab] at hw ⊢
        have ha_lt : a < w := by rw [hwk]; exact hrb a (by rw [hab]; simp)
        have hb_lt : b < w := by rw [hwk]; exact hrb b (by rw [hab]; simp)
        rcases hop with h | h <;> rw [h] at hw ⊢
        · simp only [gateOp_and_eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true] at hw ⊢
          exact ⟨ih a ha_lt hw.1, ih b hb_lt hw.2⟩
        · simp only [gateOp_or_eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.or_eq_true] at hw ⊢
          rcases hw with ha | hb
          · exact Or.inl (ih a ha_lt ha)
          · exact Or.inr (ih b hb_lt hb)
      · have hge : (evalForcedW C n w₀ false z).length ≤ w := by
          rw [evalForcedW, runForced_len, forcedInit_len]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
        cases hw

private lemma evalForcedW_true_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w₀ : ℕ)
    (z : Fin n → Bool) :
    ∀ w, (C.wires (List.ofFn z)).getD w false = true →
      (evalForcedW C n w₀ true z).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wires_eq_runW] at hw
      have hpr := runW_prefix_getD [] C.gates (List.ofFn z) w (by simp; omega)
      rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil] at hw
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hw
      rw [evalForcedW_input C w₀ true z hlt]
      split_ifs <;> simp [hw]
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        rw [hwk, isAO2_gate_eval hAO _ List.length_ofFn hk] at hw
        rw [hwk, evalForcedW_gate hAO w₀ true z hk]
        split_ifs with heq
        · rfl
        · obtain ⟨hop, hlen, hrb⟩ := ao2_gate_inputs hAO hk
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
          rw [hab] at hw ⊢
          have ha_lt : a < w := by rw [hwk]; exact hrb a (by rw [hab]; simp)
          have hb_lt : b < w := by rw [hwk]; exact hrb b (by rw [hab]; simp)
          rcases hop with h | h <;> rw [h] at hw ⊢
          · simp only [gateOp_and_eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hw ⊢
            exact ⟨ih a ha_lt hw.1, ih b hb_lt hw.2⟩
          · simp only [gateOp_or_eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true] at hw ⊢
            rcases hw with ha | hb
            · exact Or.inl (ih a ha_lt ha)
            · exact Or.inr (ih b hb_lt hb)
      · have hge : (C.wires (List.ofFn z)).length ≤ w := by
          rw [wires_eq_runW, runW_len, List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
        cases hw

private lemma evalForcedW_mono_z {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w₀ : ℕ) (b₀ : Bool)
    (z₁ z₂ : Fin n → Bool) (hle : ∀ i : Fin n, z₁ i = true → z₂ i = true) :
    ∀ w, (evalForcedW C n w₀ b₀ z₁).getD w false = true →
      (evalForcedW C n w₀ b₀ z₂).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [evalForcedW_input C w₀ b₀ z₁ hlt] at hw
      rw [evalForcedW_input C w₀ b₀ z₂ hlt]
      split_ifs at hw ⊢
      · exact hw
      · exact hle ⟨w, hlt⟩ hw
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        rw [hwk, evalForcedW_gate hAO w₀ b₀ z₁ hk] at hw
        rw [hwk, evalForcedW_gate hAO w₀ b₀ z₂ hk]
        split_ifs at hw ⊢
        · exact hw
        · obtain ⟨hop, hlen, hrb⟩ := ao2_gate_inputs hAO hk
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
          rw [hab] at hw ⊢
          have ha_lt : a < w := by rw [hwk]; exact hrb a (by rw [hab]; simp)
          have hb_lt : b < w := by rw [hwk]; exact hrb b (by rw [hab]; simp)
          rcases hop with h | h <;> rw [h] at hw ⊢
          · simp only [gateOp_and_eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hw ⊢
            exact ⟨ih a ha_lt hw.1, ih b hb_lt hw.2⟩
          · simp only [gateOp_or_eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true] at hw ⊢
            rcases hw with ha | hb
            · exact Or.inl (ih a ha_lt ha)
            · exact Or.inr (ih b hb_lt hb)
      · have hge : (evalForcedW C n w₀ b₀ z₁).length ≤ w := by
          rw [evalForcedW, runForced_len, forcedInit_len]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
        cases hw

private lemma evalForcedW_eq_of_input {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w₀ : ℕ) (hw₀ : w₀ < n) (z : Fin n → Bool) :
    ∀ w, (evalForcedW C n w₀ false z).getD w false =
      (C.wires (List.ofFn (fun i : Fin n => if i.val = w₀ then false else z i))).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [evalForcedW_input C w₀ false z hlt, wires_eq_runW]
      have hpr := runW_prefix_getD [] C.gates (List.ofFn (fun i : Fin n => if i.val = w₀ then false else z i)) w (by simp; omega)
      rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil]
      simp [List.getD_eq_getElem?_getD, hlt]
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        have hne : n + k ≠ w₀ := by omega
        rw [hwk, evalForcedW_gate hAO w₀ false z hk, if_neg hne,
            isAO2_gate_eval hAO _ List.length_ofFn hk]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hi_lt : i < n + k := (ao2_gate_inputs hAO hk).2.2 i hi
        exact ih i (by omega)
      · have hge1 : (evalForcedW C n w₀ false z).length ≤ w := by
          rw [evalForcedW, runForced_len, forcedInit_len]; omega
        have hge2 : (C.wires (List.ofFn (fun i : Fin n => if i.val = w₀ then false else z i))).length ≤ w := by
          rw [wires_eq_runW, runW_len, List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]

private lemma eval_eq_forced_outside_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g₀ : ℕ) (hg₀ : n ≤ g₀) (reach : ℕ → Prop)
    (hreach_step : ∀ j : Fin C.size, reach (n + j.val) → ∀ a ∈ (C.gates[j.val]'j.isLt).inputs, reach a)
    (huniq_cone : ∀ w < g₀, Relation.ReflTransGen (stepR C n) w g₀ →
      ∀ j₁ j₂ : Fin C.size, reach (n + j₁.val) → reach (n + j₂.val) →
      w ∈ (C.gates[j₁.val]'j₁.isLt).inputs → w ∈ (C.gates[j₂.val]'j₂.isLt).inputs → j₁ = j₂)
    (hg₀_reach : reach g₀)
    (z : Fin n → Bool) (z_out : Fin n → Bool)
    (hz_out : ∀ i : Fin n, ¬ Relation.ReflTransGen (stepR C n) i.val g₀ → z_out i = z i) :
    ∀ w, reach w → ¬ Relation.ReflTransGen (stepR C n) w g₀ →
      (C.wires (List.ofFn z)).getD w false =
        (evalForcedW C n g₀ ((C.wires (List.ofFn z)).getD g₀ false) z_out).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hreach hnc
    by_cases hlt : w < n
    · rw [evalForcedW_input C g₀ _ z_out hlt, if_neg (by omega)]
      rw [wires_eq_runW]
      have hpr := runW_prefix_getD [] C.gates (List.ofFn z) w (by simp; omega)
      rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
      exact (hz_out ⟨w, hlt⟩ hnc).symm
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        have hne : n + k ≠ g₀ := fun heq => hnc (hwk ▸ heq ▸ Relation.ReflTransGen.refl)
        rw [hwk, evalForcedW_gate hAO g₀ _ z_out hk, if_neg hne,
            isAO2_gate_eval hAO _ List.length_ofFn hk]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hi_lt : i < n + k := (ao2_gate_inputs hAO hk).2.2 i hi
        by_cases hig : i = g₀
        · subst i
          by_cases hg_lt : g₀ < n
          · omega
          · by_cases hg_ltg : g₀ < n + C.gates.length
            · let kg := g₀ - n
              have hkg : kg < C.gates.length := by omega
              have hfg := evalForcedW_gate hAO g₀ ((C.wires (List.ofFn z)).getD g₀ false) z_out hkg
              rw [if_pos (by omega), show n + kg = g₀ by omega] at hfg
              exact hfg.symm
            · have hge1 : (C.wires (List.ofFn z)).length ≤ g₀ := by
                rw [wires_eq_runW, runW_len, List.length_ofFn]; omega
              have hge2 : (evalForcedW C n g₀ ((C.wires (List.ofFn z)).getD g₀ false) z_out).length ≤ g₀ := by
                rw [evalForcedW, runForced_len, forcedInit_len]; omega
              rw [List.getD_eq_getElem?_getD (l := evalForcedW _ _ _ _ _), List.getElem?_eq_none hge2,
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1]
        · have hi_nc : ¬ Relation.ReflTransGen (stepR C n) i g₀ := by
            intro hic
            rcases Relation.ReflTransGen.cases_head hic with rfl | ⟨u, ⟨j, hu, hin⟩, huc⟩
            · exact hig rfl
            · have hcone_reach : ∀ x, Relation.ReflTransGen (stepR C n) x g₀ → reach x := by
                intro x hx
                induction hx using Relation.ReflTransGen.head_induction_on with
                | refl => exact hg₀_reach
                | head hs _ ih' =>
                  obtain ⟨j', rfl, hin'⟩ := hs
                  exact hreach_step j' ih' _ hin'
              have hj_reach : reach (n + j.val) := hcone_reach _ (hu ▸ huc)
              have hi_lt_g : i < g₀ := by
                have h1 := (ao2_gate_inputs hAO j.isLt).2.2 i hin
                have h2 := cone_le hAO (hu ▸ huc)
                omega
              have hj_eq := huniq_cone i hi_lt_g hic j ⟨k, hk⟩ hj_reach (hwk ▸ hreach) hin hi
              have hwk_eq : w = n + j.val := by rw [hwk, hj_eq]
              exact hnc (hwk_eq ▸ hu ▸ huc)
          exact ih i (by omega) (hreach_step ⟨k, hk⟩ (hwk ▸ hreach) i hi) hi_nc
      · have hge1 : (C.wires (List.ofFn z)).length ≤ w := by
          rw [wires_eq_runW, runW_len, List.length_ofFn]; omega
        have hge2 : (evalForcedW C n g₀ ((C.wires (List.ofFn z)).getD g₀ false) z_out).length ≤ w := by
          rw [evalForcedW, runForced_len, forcedInit_len]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]

private lemma forced_false_eq_outside_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g₀ : ℕ) (hg₀ : n ≤ g₀) (reach : ℕ → Prop)
    (hreach_step : ∀ j : Fin C.size, reach (n + j.val) → ∀ a ∈ (C.gates[j.val]'j.isLt).inputs, reach a)
    (huniq_cone : ∀ w < g₀, Relation.ReflTransGen (stepR C n) w g₀ →
      ∀ j₁ j₂ : Fin C.size, reach (n + j₁.val) → reach (n + j₂.val) →
      w ∈ (C.gates[j₁.val]'j₁.isLt).inputs → w ∈ (C.gates[j₂.val]'j₂.isLt).inputs → j₁ = j₂)
    (hg₀_reach : reach g₀)
    (z : Fin n → Bool) (z_out : Fin n → Bool)
    (hz_out : ∀ i : Fin n, ¬ Relation.ReflTransGen (stepR C n) i.val g₀ → z_out i = z i) :
    ∀ w, reach w → ¬ Relation.ReflTransGen (stepR C n) w g₀ →
      (evalForcedW C n g₀ false z).getD w false =
        (evalForcedW C n g₀ false z_out).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hreach hnc
    by_cases hlt : w < n
    · rw [evalForcedW_input C g₀ false z hlt, evalForcedW_input C g₀ false z_out hlt,
          if_neg (by omega), if_neg (by omega)]
      exact (hz_out ⟨w, hlt⟩ hnc).symm
    · by_cases hltg : w < n + C.gates.length
      · let k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        have hne : n + k ≠ g₀ := fun heq => hnc (hwk ▸ heq ▸ Relation.ReflTransGen.refl)
        rw [hwk, evalForcedW_gate hAO g₀ false z hk, evalForcedW_gate hAO g₀ false z_out hk,
            if_neg hne, if_neg hne]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hi_lt : i < n + k := (ao2_gate_inputs hAO hk).2.2 i hi
        by_cases hig : i = g₀
        · subst i
          by_cases hg_lt : g₀ < n
          · omega
          · by_cases hg_ltg : g₀ < n + C.gates.length
            · let kg := g₀ - n
              have hkg : kg < C.gates.length := by omega
              have hfg1 := evalForcedW_gate hAO g₀ false z hkg
              rw [if_pos (by omega), show n + kg = g₀ by omega] at hfg1
              have hfg2 := evalForcedW_gate hAO g₀ false z_out hkg
              rw [if_pos (by omega), show n + kg = g₀ by omega] at hfg2
              rw [hfg1, hfg2]
            · have hge1 : (evalForcedW C n g₀ false z).length ≤ g₀ := by
                rw [evalForcedW, runForced_len, forcedInit_len]; omega
              have hge2 : (evalForcedW C n g₀ false z_out).length ≤ g₀ := by
                rw [evalForcedW, runForced_len, forcedInit_len]; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
        · have hi_nc : ¬ Relation.ReflTransGen (stepR C n) i g₀ := by
            intro hic
            rcases Relation.ReflTransGen.cases_head hic with rfl | ⟨u, ⟨j, hu, hin⟩, huc⟩
            · exact hig rfl
            · have hcone_reach : ∀ x, Relation.ReflTransGen (stepR C n) x g₀ → reach x := by
                intro x hx
                induction hx using Relation.ReflTransGen.head_induction_on with
                | refl => exact hg₀_reach
                | head hs _ ih' =>
                  obtain ⟨j', rfl, hin'⟩ := hs
                  exact hreach_step j' ih' _ hin'
              have hj_reach : reach (n + j.val) := hcone_reach _ (hu ▸ huc)
              have hi_lt_g : i < g₀ := by
                have h1 := (ao2_gate_inputs hAO j.isLt).2.2 i hin
                have h2 := cone_le hAO (hu ▸ huc)
                omega
              have hj_eq := huniq_cone i hi_lt_g hic j ⟨k, hk⟩ hj_reach (hwk ▸ hreach) hin hi
              have hwk_eq : w = n + j.val := by rw [hwk, hj_eq]
              exact hnc (hwk_eq ▸ hu ▸ huc)
          exact ih i (by omega) (hreach_step ⟨k, hk⟩ (hwk ▸ hreach) i hi) hi_nc
      · have hge1 : (evalForcedW C n g₀ false z).length ≤ w := by
          rw [evalForcedW, runForced_len, forcedInit_len]; omega
        have hge2 : (evalForcedW C n g₀ false z_out).length ≤ w := by
          rw [evalForcedW, runForced_len, forcedInit_len]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]



private def stepS (C : Circuit) (n w₀ : ℕ) :
    (List Gate × List ℕ × (ℕ → Option ℕ)) → ℕ → (List Gate × List ℕ × (ℕ → Option ℕ)) :=
  fun st k =>
    let gs := st.1
    let emits := st.2.1
    let mp := st.2.2
    if n + k = w₀ then
      (gs, emits, Function.update mp (n + k) none)
    else
      let g := C.gates.getD k ⟨GateOp.or, []⟩
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      match g.op with
      | GateOp.and =>
        match mp a, mp b with
        | some a', some b' =>
          (gs ++ [⟨GateOp.and, [a', b']⟩], emits ++ [k], Function.update mp (n + k) (some (n + gs.length)))
        | _, _ => (gs, emits, Function.update mp (n + k) none)
      | _ =>
        match mp a, mp b with
        | some a', some b' =>
          (gs ++ [⟨GateOp.or, [a', b']⟩], emits ++ [k], Function.update mp (n + k) (some (n + gs.length)))
        | some a', none => (gs, emits, Function.update mp (n + k) (some a'))
        | none, some b' => (gs, emits, Function.update mp (n + k) (some b'))
        | none, none => (gs, emits, Function.update mp (n + k) none)

private lemma simplify_wire (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (w₀ : ℕ)
    (hw₀_lt : w₀ < n + C.gates.length) :
    ∃ (gs : List Gate) (emits : List ℕ) (mp : ℕ → Option ℕ),
      gs.length = emits.length ∧
      gs.length ≤ C.gates.length ∧
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
      (∀ j < gs.length, ∃ hj : emits.getD j 0 < C.gates.length,
        mp (n + emits.getD j 0) = some (n + j) ∧
        n + emits.getD j 0 ≠ w₀ ∧
        ∃ a b a' b', (C.gates[emits.getD j 0]'hj).inputs = [a, b] ∧
          mp a = some a' ∧ mp b = some b' ∧
          gs.getD j ⟨GateOp.or, []⟩ = ⟨(C.gates[emits.getD j 0]'hj).op, [a', b']⟩) ∧
      mp w₀ = none ∧
      (∀ w < n + C.gates.length, ∀ w', mp w = some w' → w' < n + gs.length ∧
        ((w < n ∧ w' = w) ∨
         (∃ j' < gs.length, w = n + emits.getD j' 0 ∧ w' = n + j') ∨
         (∃ j : ℕ, ∃ hj : j < C.gates.length, w = n + j ∧ n + j ≠ w₀ ∧
           (C.gates[j]'hj).op = GateOp.or ∧
           (∀ j' < gs.length, j ≠ emits.getD j' 0) ∧
           ∃ c : Fin 2, mp ((C.gates[j]'hj).inputs.getD c.val 0) = some w')) ∧
        Relation.ReflTransGen (stepR C n)
          (if w' < n then w' else n + emits.getD (w' - n) 0) w) ∧
      (∀ z : Fin n → Bool, ∀ w < n + C.gates.length,
        (evalForcedW C n w₀ false z).getD w false =
          match mp w with
          | none => false
          | some w' => (runW gs (List.ofFn z)).getD w' false) := by
  classical
  let buildS : ℕ → (List Gate × List ℕ × (ℕ → Option ℕ)) := fun k =>
    (List.range k).foldl (stepS C n w₀) ([], [], fun i => if i = w₀ then none else some i)
  have hbuild_succ : ∀ k, buildS (k + 1) = stepS C n w₀ (buildS k) k := by
    intro k
    simp [buildS, List.range_succ]
  have hInv : ∀ k ≤ C.gates.length,
      let st := buildS k
      let gs := st.1
      let emits := st.2.1
      let mp := st.2.2
      gs.length = emits.length ∧
      gs.length ≤ k ∧
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ j < gs.length, ∀ i ∈ (gs.getD j (Gate.mk GateOp.or [])).inputs, i < n + j) ∧
      (∀ j < gs.length, emits.getD j 0 < k ∧
        mp (n + emits.getD j 0) = some (n + j) ∧
        n + emits.getD j 0 ≠ w₀ ∧
        ∃ a b a' b', (C.gates.getD (emits.getD j 0) (Gate.mk GateOp.or [])).inputs = [a, b] ∧
          mp a = some a' ∧ mp b = some b' ∧
          gs.getD j (Gate.mk GateOp.or []) = Gate.mk (C.gates.getD (emits.getD j 0) (Gate.mk GateOp.or [])).op [a', b']) ∧
      (w₀ < n + k → mp w₀ = none) ∧
      (∀ w < n + k, ∀ w', mp w = some w' → w' < n + gs.length ∧
        ((w < n ∧ w' = w) ∨
         (∃ j' < gs.length, w = n + emits.getD j' 0 ∧ w' = n + j') ∨
         (∃ j : ℕ, j < k ∧ w = n + j ∧ n + j ≠ w₀ ∧
           (C.gates.getD j (Gate.mk GateOp.or [])).op = GateOp.or ∧
           (∀ j' < gs.length, j ≠ emits.getD j' 0) ∧
           ∃ c : Fin 2, mp ((C.gates.getD j (Gate.mk GateOp.or [])).inputs.getD c.val 0) = some w')) ∧
        Relation.ReflTransGen (stepR C n)
          (if w' < n then w' else n + emits.getD (w' - n) 0) w) ∧
      (∀ z : Fin n → Bool, ∀ w < n + k,
        (evalForcedW C n w₀ false z).getD w false =
          match mp w with
          | none => false
          | some w' => (runW gs (List.ofFn z)).getD w' false) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨rfl, le_rfl, by simp [buildS], by simp [buildS], by simp [buildS], ?_, ?_, ?_⟩
      · intro hw₀; simp [buildS]
      · intro w hw w' hmp
        simp only [buildS, List.range_zero, List.foldl_nil] at hmp ⊢
        by_cases heq : w = w₀
        · simp [heq] at hmp
        · simp only [heq, ↓reduceIte, Option.some.injEq] at hmp
          subst hmp
          refine ⟨by omega, Or.inl ⟨by omega, rfl⟩, ?_⟩
          have hwn : w < n := by omega
          simp [hwn, Relation.ReflTransGen.refl]
      · intro z w hw
        simp only [buildS, List.range_zero, List.foldl_nil, Nat.add_zero, runW_nil] at hw ⊢
        rw [evalForcedW_input C w₀ false z hw]
        split_ifs with heq
        · rfl
        · simp [List.getD_eq_getElem?_getD, hw]
    | succ k ih =>
      intro hk
      obtain ⟨helen, hsz, hao, hrb, hemit, hw₀_none, hmp_info, heval⟩ := ih (Nat.le_of_succ_le hk)
      set gs := (buildS k).1
      set emits := (buildS k).2.1
      set mp := (buildS k).2.2
      have hklt : k < C.gates.length := Nat.lt_of_succ_le hk
      obtain ⟨hop, hlen, hrb_k⟩ := ao2_gate_inputs hAO hklt
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
      have ha_lt : a < n + k := hrb_k a (by rw [hab]; simp)
      have hb_lt : b < n + k := hrb_k b (by rw [hab]; simp)
      have hg_eq : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]'hklt := List.getD_eq_getElem C.gates _ hklt
      have ha_get : (C.gates[k]'hklt).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (C.gates[k]'hklt).inputs.getD 1 0 = b := by rw [hab]; rfl
      have hk_no_emit : ∀ j' < gs.length, k ≠ emits.getD j' 0 := by
        intro j' hj' heq
        have := (hemit j' hj').1
        omega
      rw [hbuild_succ]
      change let st := stepS C n w₀ (gs, emits, mp) k; _
      have hupd_emit : ∀ (mp' : ℕ → Option ℕ), (∀ w < n + k, mp' w = mp w) →
          ∀ j < gs.length, emits.getD j 0 < k + 1 ∧
            mp' (n + emits.getD j 0) = some (n + j) ∧
            n + emits.getD j 0 ≠ w₀ ∧
            ∃ a₁ b₁ a' b', (C.gates.getD (emits.getD j 0) (Gate.mk GateOp.or [])).inputs = [a₁, b₁] ∧
              mp' a₁ = some a' ∧ mp' b₁ = some b' ∧
              gs.getD j (Gate.mk GateOp.or []) = Gate.mk (C.gates.getD (emits.getD j 0) (Gate.mk GateOp.or [])).op [a', b'] := by
        intro mp' hmp' j hj
        obtain ⟨hjlt, hmpe, hne, a₁, b₁, a', b', hinp, ha1, hb1, hgsj⟩ := hemit j hj
        have hC_em : C.gates.getD (emits.getD j 0) (Gate.mk GateOp.or []) = C.gates[emits.getD j 0]'(by omega) :=
          List.getD_eq_getElem C.gates _ (by omega)
        have ha1_lt : a₁ < n + emits.getD j 0 := by
          rw [hC_em] at hinp
          exact (ao2_gate_inputs hAO (show emits.getD j 0 < C.gates.length by omega)).2.2 a₁ (by rw [hinp]; simp)
        have hb1_lt : b₁ < n + emits.getD j 0 := by
          rw [hC_em] at hinp
          exact (ao2_gate_inputs hAO (show emits.getD j 0 < C.gates.length by omega)).2.2 b₁ (by rw [hinp]; simp)
        refine ⟨by omega, ?_, hne, a₁, b₁, a', b', hinp, ?_, ?_, hgsj⟩
        · rw [hmp' _ (by omega)]; exact hmpe
        · rw [hmp' _ (by omega)]; exact ha1
        · rw [hmp' _ (by omega)]; exact hb1
      have hupd_old_info : ∀ (mp' : ℕ → Option ℕ), (∀ w < n + k, mp' w = mp w) →
          ∀ w < n + k, ∀ w', mp' w = some w' → w' < n + gs.length ∧
            ((w < n ∧ w' = w) ∨
             (∃ j' < gs.length, w = n + emits.getD j' 0 ∧ w' = n + j') ∨
             (∃ j : ℕ, j < k + 1 ∧ w = n + j ∧ n + j ≠ w₀ ∧
               (C.gates.getD j (Gate.mk GateOp.or [])).op = GateOp.or ∧
               (∀ j' < gs.length, j ≠ emits.getD j' 0) ∧
               ∃ c : Fin 2, mp' ((C.gates.getD j (Gate.mk GateOp.or [])).inputs.getD c.val 0) = some w')) ∧
            Relation.ReflTransGen (stepR C n)
              (if w' < n then w' else n + emits.getD (w' - n) 0) w := by
        intro mp' hmp' w hw w' hmw
        rw [hmp' w hw] at hmw
        obtain ⟨hw'lt, hcases, hrt⟩ := hmp_info w hw w' hmw
        refine ⟨hw'lt, ?_, hrt⟩
        rcases hcases with h1 | h2 | ⟨j, hj, rfl, hne, hopj, hnoem, c, hc⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · have hjC : j < C.gates.length := by omega
          have hCj : C.gates.getD j (Gate.mk GateOp.or []) = C.gates[j]'hjC :=
            List.getD_eq_getElem C.gates _ hjC
          have hcin : (C.gates.getD j (Gate.mk GateOp.or [])).inputs.getD c.val 0 < n + j := by
            rw [hCj]
            obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO hjC).2.1
            have hmem : (C.gates[j]'hjC).inputs.getD c.val 0 ∈ (C.gates[j]'hjC).inputs := by
              fin_cases c <;> simp [hx]
            exact (ao2_gate_inputs hAO hjC).2.2 _ hmem
          refine Or.inr (Or.inr ⟨j, by omega, rfl, hne, hopj, hnoem, c, ?_⟩)
          rw [hmp' _ (by omega)]
          exact hc
      by_cases hw₀k : n + k = w₀
      · have hst : stepS C n w₀ (gs, emits, mp) k = (gs, emits, Function.update mp (n + k) none) := by
          simp [stepS, hw₀k]
        rw [hst]
        dsimp only
        have hmp_keep : ∀ w < n + k, Function.update mp (n + k) none w = mp w :=
          fun w hw => by rw [Function.update_of_ne (by omega)]
        refine ⟨helen, by omega, hao, hrb, hupd_emit _ hmp_keep, ?_, ?_, ?_⟩
        · intro _; rw [← hw₀k, Function.update_self]
        · intro w hw w' hmw
          by_cases hwk : w = n + k
          · subst hwk; simp at hmw
          · exact hupd_old_info _ hmp_keep w (by omega) w' hmw
        · intro z w hw
          by_cases hwk : w = n + k
          · subst hwk
            rw [Function.update_self, evalForcedW_gate hAO w₀ false z hklt, if_pos hw₀k]
          · rw [Function.update_of_ne (by omega)]; exact heval z w (by omega)
      · have hw₀k' : n + k ≠ w₀ := hw₀k
        have hstep_eval : ∀ z : Fin n → Bool,
            (evalForcedW C n w₀ false z).getD (n + k) false =
              (C.gates[k]'hklt).op.eval
                [match mp a with | none => false | some a' => (runW gs (List.ofFn z)).getD a' false,
                 match mp b with | none => false | some b' => (runW gs (List.ofFn z)).getD b' false] := by
          intro z
          rw [evalForcedW_gate hAO w₀ false z hklt, if_neg hw₀k', hab]
          simp only [List.map_cons, List.map_nil]
          rw [heval z a ha_lt, heval z b hb_lt]
        rcases hop with hop_and | hop_or
        · cases hma : mp a with
          | none =>
            have hst : stepS C n w₀ (gs, emits, mp) k = (gs, emits, Function.update mp (n + k) none) := by
              simp only [stepS, hw₀k', ↓reduceIte, hg_eq, hop_and]
              rw [ha_get, hma]
            rw [hst]; dsimp only
            have hmp_keep : ∀ w < n + k, Function.update mp (n + k) none w = mp w :=
              fun w hw => by rw [Function.update_of_ne (by omega)]
            refine ⟨helen, by omega, hao, hrb, hupd_emit _ hmp_keep, ?_, ?_, ?_⟩
            · intro hw₀; rw [Function.update_of_ne hw₀k'.symm]; exact hw₀_none (by omega)
            · intro w hw w' hmw
              by_cases hwk : w = n + k
              · subst hwk; simp at hmw
              · exact hupd_old_info _ hmp_keep w (by omega) w' hmw
            · intro z w hw
              by_cases hwk : w = n + k
              · subst hwk
                rw [Function.update_self, hstep_eval z, hma, hop_and]
                simp [gateOp_and_eval]
              · rw [Function.update_of_ne (by omega)]; exact heval z w (by omega)
          | some a' =>
            cases hmb : mp b with
            | none =>
              have hst : stepS C n w₀ (gs, emits, mp) k = (gs, emits, Function.update mp (n + k) none) := by
                simp only [stepS, hw₀k', ↓reduceIte, hg_eq, hop_and]
                rw [ha_get, hb_get, hma, hmb]
              rw [hst]; dsimp only
              have hmp_keep : ∀ w < n + k, Function.update mp (n + k) none w = mp w :=
                fun w hw => by rw [Function.update_of_ne (by omega)]
              refine ⟨helen, by omega, hao, hrb, hupd_emit _ hmp_keep, ?_, ?_, ?_⟩
              · intro hw₀; rw [Function.update_of_ne hw₀k'.symm]; exact hw₀_none (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw₀) hw₀k'.symm)
              · intro w hw w' hmw
                by_cases hwk : w = n + k
                · subst hwk; simp at hmw
                · exact hupd_old_info _ hmp_keep w (by omega) w' hmw
              · intro z w hw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self, hstep_eval z, hma, hmb, hop_and]
                  simp [gateOp_and_eval]
                · rw [Function.update_of_ne (by omega)]; exact heval z w (by omega)
            | some b' =>
              have hst : stepS C n w₀ (gs, emits, mp) k =
                  (gs ++ [Gate.mk GateOp.and [a', b']], emits ++ [k],
                    Function.update mp (n + k) (some (n + gs.length))) := by
                simp only [stepS, hw₀k', ↓reduceIte, hg_eq, hop_and]
                rw [ha_get, hb_get, hma, hmb]
              rw [hst]; dsimp only
              have ha'_info := hmp_info a ha_lt a' hma
              have hb'_info := hmp_info b hb_lt b' hmb
              have hmp_keep : ∀ w < n + k, Function.update mp (n + k) (some (n + gs.length)) w = mp w :=
                fun w hw => by rw [Function.update_of_ne (by omega)]
              refine ⟨by simp [helen], by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro g' hg'
                simp only [List.mem_append, List.mem_singleton] at hg'
                rcases hg' with hg' | rfl
                · exact hao g' hg'
                · exact ⟨Or.inl rfl, rfl⟩
              · intro j hj i hi
                simp only [List.length_append, List.length_singleton] at hj
                by_cases hjlt : j < gs.length
                · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt, ← List.getD_eq_getElem?_getD] at hi
                  exact hrb j hjlt i hi
                · have hjeq : j = gs.length := by omega
                  subst hjeq
                  rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
                  simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · exact ha'_info.1
                  · exact hb'_info.1
              · intro j hj
                simp only [List.length_append, List.length_singleton] at hj
                by_cases hjlt : j < gs.length
                · have he_eq : (emits ++ [k]).getD j 0 = emits.getD j 0 := by
                    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                  have hg_eq' : (gs ++ [Gate.mk GateOp.and [a', b']]).getD j (Gate.mk GateOp.or []) = gs.getD j (Gate.mk GateOp.or []) := by
                    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt, ← List.getD_eq_getElem?_getD]
                  obtain ⟨hjlt', hmpe, hne, a₁, b₁, a₁', b₁', hinp, ha1, hb1, hgsj⟩ :=
                    hupd_emit _ hmp_keep j hjlt
                  refine ⟨by rw [he_eq]; exact hjlt', ?_, ?_, a₁, b₁, a₁', b₁', ?_, ha1, hb1, ?_⟩
                  · rw [he_eq]; exact hmpe
                  · rw [he_eq]; exact hne
                  · simp only [he_eq, hinp]
                  · rw [hg_eq', hgsj]; simp only [he_eq]
                · have hjeq : j = gs.length := by omega
                  subst hjeq
                  have he_eq : (emits ++ [k]).getD gs.length 0 = k := by
                    rw [List.getD_eq_getElem?_getD, helen, List.getElem?_concat_length]; rfl
                  have hg_eq' : (gs ++ [Gate.mk GateOp.and [a', b']]).getD gs.length (Gate.mk GateOp.or []) = Gate.mk GateOp.and [a', b'] := by
                    rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length]; rfl
                  have hCk : C.gates.getD k (Gate.mk GateOp.or []) = C.gates[k]'hklt :=
                    List.getD_eq_getElem C.gates _ hklt
                  refine ⟨by rw [he_eq]; omega, ?_, ?_, a, b, a', b', ?_, ?_, ?_, ?_⟩
                  · rw [he_eq, Function.update_self]
                  · rw [he_eq]; exact hw₀k'
                  · simp only [he_eq, hCk, hab]
                  · rw [hmp_keep _ ha_lt, hma]
                  · rw [hmp_keep _ hb_lt, hmb]
                  · simp only [hg_eq', he_eq, hCk, hop_and]
              · intro hw₀; rw [Function.update_of_ne hw₀k'.symm]; exact hw₀_none (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw₀) hw₀k'.symm)
              · intro w hw w' hmw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self] at hmw
                  cases hmw
                  have he_eq : (emits ++ [k]).getD gs.length 0 = k := by
                    rw [List.getD_eq_getElem?_getD, helen, List.getElem?_concat_length]; rfl
                  refine ⟨by simp, Or.inr (Or.inl ⟨gs.length, by simp, by rw [he_eq], rfl⟩), ?_⟩
                  have hnotlt : ¬ n + gs.length < n := by omega
                  rw [if_neg hnotlt, show n + gs.length - n = gs.length by omega, he_eq]
                · obtain ⟨hw'lt, hcases, hrt⟩ := hupd_old_info _ hmp_keep w (by omega) w' hmw
                  refine ⟨by simp; omega, ?_, ?_⟩
                  · rcases hcases with h1 | ⟨j', hj', hweq, hw'eq⟩ | ⟨j, hj, hweq, hne, hopj, hnoem, c, hc⟩
                    · exact Or.inl h1
                    · refine Or.inr (Or.inl ⟨j', by simp; omega, ?_, hw'eq⟩)
                      have he_eq : (emits ++ [k]).getD j' 0 = emits.getD j' 0 := by
                        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                      rw [he_eq, hweq]
                    · refine Or.inr (Or.inr ⟨j, hj, hweq, hne, hopj, ?_, c, hc⟩)
                      intro j' hj'
                      simp only [List.length_append, List.length_singleton] at hj'
                      by_cases hj'lt : j' < gs.length
                      · have he_eq : (emits ++ [k]).getD j' 0 = emits.getD j' 0 := by
                          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                        rw [he_eq]; exact hnoem j' hj'lt
                      · have hj'eq : j' = gs.length := by omega
                        subst hj'eq
                        have he_eq : (emits ++ [k]).getD gs.length 0 = k := by
                          rw [List.getD_eq_getElem?_getD, helen, List.getElem?_concat_length]; rfl
                        rw [he_eq]; omega
                  · by_cases hw'n : w' < n
                    · simpa [hw'n] using hrt
                    · rw [if_neg hw'n] at hrt ⊢
                      have he_eq : (emits ++ [k]).getD (w' - n) 0 = emits.getD (w' - n) 0 := by
                        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                      rw [he_eq]; exact hrt
              · intro z w hw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self, hstep_eval z, hma, hmb, hop_and]
                  dsimp only
                  rw [runW_snoc]
                  have hlenw : (runW gs (List.ofFn z)).length = n + gs.length := by
                    rw [runW_len, List.length_ofFn]
                  simp [List.getD_eq_getElem?_getD, hlenw, gateOp_and_eval]
                · rw [Function.update_of_ne (by omega), heval z w (by omega)]
                  cases hmw : mp w with
                  | none => rfl
                  | some w' =>
                    have hw'lt := (hmp_info w (by omega) w' hmw).1
                    dsimp only
                    rw [runW_prefix_getD gs [Gate.mk GateOp.and [a', b']] (List.ofFn z) w' (by simp; omega)]
        · -- OR gate case
          cases hma : mp a with
          | none =>
            cases hmb : mp b with
            | none =>
              have hst : stepS C n w₀ (gs, emits, mp) k = (gs, emits, Function.update mp (n + k) none) := by
                simp only [stepS, hw₀k', ↓reduceIte, hg_eq, hop_or]
                rw [ha_get, hb_get, hma, hmb]
              rw [hst]; dsimp only
              have hmp_keep : ∀ w < n + k, Function.update mp (n + k) none w = mp w :=
                fun w hw => by rw [Function.update_of_ne (by omega)]
              refine ⟨helen, by omega, hao, hrb, hupd_emit _ hmp_keep, ?_, ?_, ?_⟩
              · intro hw₀; rw [Function.update_of_ne hw₀k'.symm]; exact hw₀_none (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw₀) hw₀k'.symm)
              · intro w hw w' hmw
                by_cases hwk : w = n + k
                · subst hwk; simp at hmw
                · exact hupd_old_info _ hmp_keep w (by omega) w' hmw
              · intro z w hw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self, hstep_eval z, hma, hmb, hop_or]
                  simp [gateOp_or_eval]
                · rw [Function.update_of_ne (by omega)]; exact heval z w (by omega)
            | some b' =>
              have hst : stepS C n w₀ (gs, emits, mp) k = (gs, emits, Function.update mp (n + k) (some b')) := by
                simp only [stepS, hw₀k', ↓reduceIte, hg_eq, hop_or]
                rw [ha_get, hb_get, hma, hmb]
              rw [hst]; dsimp only
              have hb'_info := hmp_info b hb_lt b' hmb
              have hmp_keep : ∀ w < n + k, Function.update mp (n + k) (some b') w = mp w :=
                fun w hw => by rw [Function.update_of_ne (by omega)]
              refine ⟨helen, by omega, hao, hrb, hupd_emit _ hmp_keep, ?_, ?_, ?_⟩
              · intro hw₀; rw [Function.update_of_ne hw₀k'.symm]; exact hw₀_none (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw₀) hw₀k'.symm)
              · intro w hw w' hmw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self] at hmw
                  cases hmw
                  have hCk : C.gates.getD k (Gate.mk GateOp.or []) = C.gates[k]'hklt :=
                    List.getD_eq_getElem C.gates _ hklt
                  refine ⟨hb'_info.1, Or.inr (Or.inr ⟨k, Nat.lt_succ_self k, rfl, hw₀k', by rw [hCk]; exact hop_or, hk_no_emit, 1, ?_⟩), ?_⟩
                  · rw [hCk, show ((1 : Fin 2) : ℕ) = 1 from rfl, hb_get, hmp_keep _ hb_lt, hmb]
                  · exact Relation.ReflTransGen.tail hb'_info.2.2 ⟨⟨k, hklt⟩, rfl, by change b ∈ (C.gates[k]'hklt).inputs; rw [hab]; simp⟩
                · exact hupd_old_info _ hmp_keep w (by omega) w' hmw
              · intro z w hw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self, hstep_eval z, hma, hmb, hop_or]
                  simp [gateOp_or_eval]
                · rw [Function.update_of_ne (by omega)]; exact heval z w (by omega)
          | some a' =>
            cases hmb : mp b with
            | none =>
              have hst : stepS C n w₀ (gs, emits, mp) k = (gs, emits, Function.update mp (n + k) (some a')) := by
                simp only [stepS, hw₀k', ↓reduceIte, hg_eq, hop_or]
                rw [ha_get, hb_get, hma, hmb]
              rw [hst]; dsimp only
              have ha'_info := hmp_info a ha_lt a' hma
              have hmp_keep : ∀ w < n + k, Function.update mp (n + k) (some a') w = mp w :=
                fun w hw => by rw [Function.update_of_ne (by omega)]
              refine ⟨helen, by omega, hao, hrb, hupd_emit _ hmp_keep, ?_, ?_, ?_⟩
              · intro hw₀; rw [Function.update_of_ne hw₀k'.symm]; exact hw₀_none (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw₀) hw₀k'.symm)
              · intro w hw w' hmw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self] at hmw
                  cases hmw
                  have hCk : C.gates.getD k (Gate.mk GateOp.or []) = C.gates[k]'hklt :=
                    List.getD_eq_getElem C.gates _ hklt
                  refine ⟨ha'_info.1, Or.inr (Or.inr ⟨k, Nat.lt_succ_self k, rfl, hw₀k', by rw [hCk]; exact hop_or, hk_no_emit, 0, ?_⟩), ?_⟩
                  · rw [hCk, show ((0 : Fin 2) : ℕ) = 0 from rfl, ha_get, hmp_keep _ ha_lt, hma]
                  · exact Relation.ReflTransGen.tail ha'_info.2.2 ⟨⟨k, hklt⟩, rfl, by change a ∈ (C.gates[k]'hklt).inputs; rw [hab]; simp⟩
                · exact hupd_old_info _ hmp_keep w (by omega) w' hmw
              · intro z w hw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self, hstep_eval z, hma, hmb, hop_or]
                  simp [gateOp_or_eval]
                · rw [Function.update_of_ne (by omega)]; exact heval z w (by omega)
            | some b' =>
              have hst : stepS C n w₀ (gs, emits, mp) k =
                  (gs ++ [Gate.mk GateOp.or [a', b']], emits ++ [k],
                    Function.update mp (n + k) (some (n + gs.length))) := by
                simp only [stepS, hw₀k', ↓reduceIte, hg_eq, hop_or]
                rw [ha_get, hb_get, hma, hmb]
              rw [hst]; dsimp only
              have ha'_info := hmp_info a ha_lt a' hma
              have hb'_info := hmp_info b hb_lt b' hmb
              have hmp_keep : ∀ w < n + k, Function.update mp (n + k) (some (n + gs.length)) w = mp w :=
                fun w hw => by rw [Function.update_of_ne (by omega)]
              refine ⟨by simp [helen], by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro g' hg'
                simp only [List.mem_append, List.mem_singleton] at hg'
                rcases hg' with hg' | rfl
                · exact hao g' hg'
                · exact ⟨Or.inr rfl, rfl⟩
              · intro j hj i hi
                simp only [List.length_append, List.length_singleton] at hj
                by_cases hjlt : j < gs.length
                · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt, ← List.getD_eq_getElem?_getD] at hi
                  exact hrb j hjlt i hi
                · have hjeq : j = gs.length := by omega
                  subst hjeq
                  rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
                  simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · exact ha'_info.1
                  · exact hb'_info.1
              · intro j hj
                simp only [List.length_append, List.length_singleton] at hj
                by_cases hjlt : j < gs.length
                · have he_eq : (emits ++ [k]).getD j 0 = emits.getD j 0 := by
                    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                  have hg_eq' : (gs ++ [Gate.mk GateOp.or [a', b']]).getD j (Gate.mk GateOp.or []) = gs.getD j (Gate.mk GateOp.or []) := by
                    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt, ← List.getD_eq_getElem?_getD]
                  obtain ⟨hjlt', hmpe, hne, a₁, b₁, a₁', b₁', hinp, ha1, hb1, hgsj⟩ :=
                    hupd_emit _ hmp_keep j hjlt
                  refine ⟨by rw [he_eq]; exact hjlt', ?_, ?_, a₁, b₁, a₁', b₁', ?_, ha1, hb1, ?_⟩
                  · rw [he_eq]; exact hmpe
                  · rw [he_eq]; exact hne
                  · simp only [he_eq, hinp]
                  · rw [hg_eq', hgsj]; simp only [he_eq]
                · have hjeq : j = gs.length := by omega
                  subst hjeq
                  have he_eq : (emits ++ [k]).getD gs.length 0 = k := by
                    rw [List.getD_eq_getElem?_getD, helen, List.getElem?_concat_length]; rfl
                  have hg_eq' : (gs ++ [Gate.mk GateOp.or [a', b']]).getD gs.length (Gate.mk GateOp.or []) = Gate.mk GateOp.or [a', b'] := by
                    rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length]; rfl
                  have hCk : C.gates.getD k (Gate.mk GateOp.or []) = C.gates[k]'hklt :=
                    List.getD_eq_getElem C.gates _ hklt
                  refine ⟨by rw [he_eq]; omega, ?_, ?_, a, b, a', b', ?_, ?_, ?_, ?_⟩
                  · rw [he_eq, Function.update_self]
                  · rw [he_eq]; exact hw₀k'
                  · simp only [he_eq, hCk, hab]
                  · rw [hmp_keep _ ha_lt, hma]
                  · rw [hmp_keep _ hb_lt, hmb]
                  · simp only [hg_eq', he_eq, hCk, hop_or]
              · intro hw₀; rw [Function.update_of_ne hw₀k'.symm]; exact hw₀_none (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw₀) hw₀k'.symm)
              · intro w hw w' hmw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self] at hmw
                  cases hmw
                  have he_eq : (emits ++ [k]).getD gs.length 0 = k := by
                    rw [List.getD_eq_getElem?_getD, helen, List.getElem?_concat_length]; rfl
                  refine ⟨by simp, Or.inr (Or.inl ⟨gs.length, by simp, by rw [he_eq], rfl⟩), ?_⟩
                  have hnotlt : ¬ n + gs.length < n := by omega
                  rw [if_neg hnotlt, show n + gs.length - n = gs.length by omega, he_eq]
                · obtain ⟨hw'lt, hcases, hrt⟩ := hupd_old_info _ hmp_keep w (by omega) w' hmw
                  refine ⟨by simp; omega, ?_, ?_⟩
                  · rcases hcases with h1 | ⟨j', hj', hweq, hw'eq⟩ | ⟨j, hj, hweq, hne, hopj, hnoem, c, hc⟩
                    · exact Or.inl h1
                    · refine Or.inr (Or.inl ⟨j', by simp; omega, ?_, hw'eq⟩)
                      have he_eq : (emits ++ [k]).getD j' 0 = emits.getD j' 0 := by
                        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                      rw [he_eq, hweq]
                    · refine Or.inr (Or.inr ⟨j, hj, hweq, hne, hopj, ?_, c, hc⟩)
                      intro j' hj'
                      simp only [List.length_append, List.length_singleton] at hj'
                      by_cases hj'lt : j' < gs.length
                      · have he_eq : (emits ++ [k]).getD j' 0 = emits.getD j' 0 := by
                          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                        rw [he_eq]; exact hnoem j' hj'lt
                      · have hj'eq : j' = gs.length := by omega
                        subst hj'eq
                        have he_eq : (emits ++ [k]).getD gs.length 0 = k := by
                          rw [List.getD_eq_getElem?_getD, helen, List.getElem?_concat_length]; rfl
                        rw [he_eq]; omega
                  · by_cases hw'n : w' < n
                    · simpa [hw'n] using hrt
                    · rw [if_neg hw'n] at hrt ⊢
                      have he_eq : (emits ++ [k]).getD (w' - n) 0 = emits.getD (w' - n) 0 := by
                        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
                      rw [he_eq]; exact hrt
              · intro z w hw
                by_cases hwk : w = n + k
                · subst hwk
                  rw [Function.update_self, hstep_eval z, hma, hmb, hop_or]
                  dsimp only
                  rw [runW_snoc]
                  have hlenw : (runW gs (List.ofFn z)).length = n + gs.length := by
                    rw [runW_len, List.length_ofFn]
                  simp [List.getD_eq_getElem?_getD, hlenw, gateOp_or_eval]
                · rw [Function.update_of_ne (by omega), heval z w (by omega)]
                  cases hmw : mp w with
                  | none => rfl
                  | some w' =>
                    have hw'lt := (hmp_info w (by omega) w' hmw).1
                    dsimp only
                    rw [runW_prefix_getD gs [Gate.mk GateOp.or [a', b']] (List.ofFn z) w' (by simp; omega)]
  obtain ⟨helen, hsz, hao, hrb, hemit, hw₀_none, hmp_info, heval⟩ := hInv C.gates.length le_rfl
  refine ⟨(buildS C.gates.length).1, (buildS C.gates.length).2.1, (buildS C.gates.length).2.2,
    helen, hsz, hao, hrb, ?_, hw₀_none hw₀_lt, ?_, heval⟩
  · intro j hj
    obtain ⟨hjlt, h1, h2, a, b, a', b', h3, h4, h5, h6⟩ := hemit j hj
    have hC_em : C.gates.getD ((buildS C.gates.length).2.1.getD j 0) (Gate.mk GateOp.or []) =
        C.gates[(buildS C.gates.length).2.1.getD j 0]'hjlt :=
      List.getD_eq_getElem C.gates _ hjlt
    rw [hC_em] at h3 h6
    exact ⟨hjlt, h1, h2, a, b, a', b', h3, h4, h5, h6⟩
  · intro w hw w' hmw
    obtain ⟨hw'lt, hcases, hrt⟩ := hmp_info w hw w' hmw
    refine ⟨hw'lt, ?_, hrt⟩
    rcases hcases with h1 | h2 | ⟨j, hj, h3, h4, h5, h6, h7⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · have hCj : C.gates.getD j (Gate.mk GateOp.or []) = C.gates[j]'hj :=
        List.getD_eq_getElem C.gates _ hj
      rw [hCj] at h5 h7
      exact Or.inr (Or.inr ⟨j, hj, h3, h4, h5, h6, h7⟩)



open Classical in
private lemma branching_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hcol : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hrow : ∀ p : Fin N, Fintype.card { l : Fin N // I p l } = q + 1)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l')) :
    ∀ B : ℕ, ∀ C : Circuit, IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      ∀ ET : Finset (Fin N × Fin N),
        (∀ e ∈ ET, I e.1 e.2 ∧
          circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
        let n := N + N
        let reach : ℕ → Prop := fun a => Relation.ReflTransGen (stepR C n) a C.output
        let R : Finset (Fin C.size) := Finset.univ.filter fun j => reach (n + j.val)
        let Sread : Finset ℕ := R.biUnion fun j => (C.gates[j.val]'j.isLt).inputs.toFinset
        let deg : ℕ → ℕ := fun w =>
          ((R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
            (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w).card
        B = ∑ w ∈ Sread, (deg w - 1) →
        ET.card ≤ (ET.image Prod.fst).card + (ET.image Prod.snd).card + (q + 1) * B ∧
        (ET.image Prod.fst).card + (ET.image Prod.snd).card + B ≤ C.size + 1 := by
  classical
  intro B
  induction B using Nat.strong_induction_on with
  | ind B ih =>
    intro C hAO hsound ET hET n reach R Sread deg hB
    let edge : Fin N → Fin N → Fin n → Bool := fun p l k =>
      decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
    let onlyP : Fin N → Fin n → Bool := fun p k => decide (k = Fin.castAdd N p)
    let onlyL : Fin N → Fin n → Bool := fun l k => decide (k = Fin.natAdd N l)
    have hsound_p : ∀ p : Fin N, circuitFun n C (onlyP p) = false := by
      intro p
      apply hsound (onlyP p)
      · rw [Fintype.card_subtype]
        have hemp : Finset.univ.filter (fun l : Fin N => onlyP p (Fin.natAdd N l) = true) = ∅ := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            onlyP, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
          omega
        rw [hemp]; simp
      · rintro ⟨_, l, _, _, hl⟩
        simp only [onlyP, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl
        omega
    have hsound_l : ∀ l : Fin N, circuitFun n C (onlyL l) = false := by
      intro l
      apply hsound (onlyL l)
      · rw [Fintype.card_subtype]
        have hsub : Finset.univ.filter (fun l' : Fin N => onlyL l (Fin.natAdd N l') = true) ⊆ {l} := by
          intro l' hl'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, onlyL, decide_eq_true_eq] at hl'
          have hv := congrArg Fin.val hl'
          simp only [Fin.val_natAdd] at hv
          exact Finset.mem_singleton.mpr (Fin.ext (by omega))
        exact (Finset.card_le_card hsub).trans (by simp; omega)
      · rintro ⟨p, _, _, hp, _⟩
        simp only [onlyL, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp
        omega
    have hdeg_pos : ∀ w ∈ Sread, 1 ≤ deg w := by
      intro w hw
      obtain ⟨j, hjR, hwj⟩ := Finset.mem_biUnion.mp hw
      rw [List.mem_toFinset] at hwj
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j.isLt).2.1
      rw [hab] at hwj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwj
      refine Finset.card_pos.mpr ?_
      rcases hwj with rfl | rfl
      · exact ⟨(j, 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hjR, Finset.mem_univ _⟩, by simp [hab]⟩⟩
      · exact ⟨(j, 1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hjR, Finset.mem_univ _⟩, by simp [hab]⟩⟩
    have hsum_deg : ∑ w ∈ Sread, deg w = 2 * R.card := by
      have hpart : ∑ w ∈ Sread, deg w = (R ×ˢ (Finset.univ : Finset (Fin 2))).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext ⟨j, c⟩
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            and_true]
          constructor
          · rintro ⟨w, _, hjR, _⟩; exact hjR
          · intro hjR
            refine ⟨(C.gates[j.val]'j.isLt).inputs.getD c.val 0, ?_, hjR, rfl⟩
            refine Finset.mem_biUnion.mpr ⟨j, hjR, ?_⟩
            rw [List.mem_toFinset]
            obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j.isLt).2.1
            fin_cases c <;> simp [hab]
        · intro w₁ _ w₂ _ hne
          rw [Function.onFun, Finset.disjoint_left]
          intro ⟨j, c⟩ h1 h2
          have e1 := (Finset.mem_filter.mp h1).2
          have e2 := (Finset.mem_filter.mp h2).2
          exact hne (e1.symm.trans e2)
      rw [hpart, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      ring
    have hB_eq : B + Sread.card = 2 * R.card := by
      rw [hB, ← hsum_deg]
      have h1 : ∀ w ∈ Sread, (deg w - 1) + 1 = deg w := fun w hw => Nat.sub_add_cancel (hdeg_pos w hw)
      calc (∑ w ∈ Sread, (deg w - 1)) + Sread.card
          = (∑ w ∈ Sread, (deg w - 1)) + ∑ _w ∈ Sread, 1 := by simp
        _ = ∑ w ∈ Sread, ((deg w - 1) + 1) := by rw [← Finset.sum_add_distrib]
        _ = ∑ w ∈ Sread, deg w := Finset.sum_congr rfl h1
    have hR_le : R.card ≤ C.size := by
      calc R.card ≤ (Finset.univ : Finset (Fin C.size)).card := Finset.card_le_univ _
        _ = C.size := Fintype.card_fin _
    let R' : Finset (Fin C.size) := R.filter fun j => n + j.val ≠ C.output
    have hR'_sub' : R'.image (fun j : Fin C.size => n + j.val) ⊆ Sread := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      have hjm := Finset.mem_filter.mp hj
      have hrj : reach (n + j.val) := (Finset.mem_filter.mp hjm.1).2
      rcases Relation.ReflTransGen.cases_head hrj with h_eq | ⟨u, ⟨j₂, hu, hjw⟩, hru⟩
      · exact absurd h_eq hjm.2
      · refine Finset.mem_biUnion.mpr ⟨j₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu ▸ hru⟩, ?_⟩
        exact List.mem_toFinset.mpr hjw
    have hR'_card : R'.card ≤ Sread.card := by
      calc R'.card = (R'.image (fun j : Fin C.size => n + j.val)).card :=
            (Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega))).symm
        _ ≤ Sread.card := Finset.card_le_card hR'_sub'
    have hR_minus_1 : R.card - 1 ≤ R'.card := by
      by_cases hex_out : ∃ j ∈ R, n + j.val = C.output
      · obtain ⟨j₀, hj₀, hjo⟩ := hex_out
        have her : R' = R.erase j₀ := by
          ext j
          simp only [R', Finset.mem_filter, Finset.mem_erase, ne_eq, Fin.ext_iff]
          constructor
          · rintro ⟨hj, hne⟩; exact ⟨by omega, hj⟩
          · rintro ⟨hne, hj⟩; exact ⟨hj, by omega⟩
        rw [her, Finset.card_erase_of_mem hj₀]
      · push Not at hex_out
        have heq : R' = R := by
          ext j
          simp only [R', Finset.mem_filter, and_iff_left_iff_imp]
          exact hex_out j
        rw [heq]; omega
    by_cases hET_emp : ET = ∅
    · subst hET_emp
      simp only [Finset.card_empty, Finset.image_empty, zero_add, zero_le, true_and]
      have hRS : R.card ≤ Sread.card + 1 := by omega
      omega
    obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hET_emp
    have hout_lt : C.output < n + C.gates.length := by
      by_contra hge
      have hge' : (C.wires (List.ofFn (edge e₀.1 e₀.2))).length ≤ C.output := by
        rw [wires_eq_runW, runW_len, List.length_ofFn]; omega
      have hf : circuitFun n C (edge e₀.1 e₀.2) = false := by
        change (C.wires (List.ofFn (edge e₀.1 e₀.2))).getD C.output false = false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge']; rfl
      have ht := (hET e₀ he₀).2
      rw [hf] at ht; cases ht
    have hout_ge : n ≤ C.output := by
      by_contra hlt
      push Not at hlt
      have hout_eval : ∀ z : Fin n → Bool, circuitFun n C z = z ⟨C.output, hlt⟩ := by
        intro z
        change (C.wires (List.ofFn z)).getD C.output false = _
        rw [wires_eq_runW]
        have hpr := runW_prefix_getD [] C.gates (List.ofFn z) C.output (by simp; omega)
        rw [show C.gates = [] ++ C.gates from rfl, hpr, runW_nil]
        simp [List.getD_eq_getElem?_getD, hlt]
      by_cases hp : C.output < N
      · have h1 := hout_eval (onlyP ⟨C.output, hp⟩)
        have h2 := hsound_p ⟨C.output, hp⟩
        rw [h2] at h1
        simp [onlyP, Fin.ext_iff] at h1
      · have h1 := hout_eval (onlyL ⟨C.output - N, by omega⟩)
        have h2 := hsound_l ⟨C.output - N, by omega⟩
        rw [h2] at h1
        have hidx : (⟨C.output, hlt⟩ : Fin (N + N)) = Fin.natAdd N ⟨C.output - N, by omega⟩ :=
          Fin.ext (by simp only [Fin.val_natAdd]; omega)
        simp only [onlyL, hidx, decide_true] at h1
        cases h1
    have hreach_in_Sread : ∀ w, reach w → w ≠ C.output → w ∈ Sread := by
      intro w hrw hne
      rcases Relation.ReflTransGen.cases_head hrw with rfl | ⟨u, ⟨j, rfl, hjw⟩, hru⟩
      · exact absurd rfl hne
      · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hru⟩, ?_⟩
        exact List.mem_toFinset.mpr hjw
    have hreach_p : ∀ p ∈ ET.image Prod.fst, reach p.val := by
      intro p hp
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      by_contra hnr
      have hag : ∀ i : Fin n, reach i.val → edge e.1 e.2 i = onlyL e.2 i := by
        intro i hri
        have hne : i ≠ Fin.castAdd N e.1 := fun heq => hnr (by simpa [Fin.ext_iff, heq] using hri)
        simp [edge, onlyL, hne]
      have heq := eval_eq_of_cone hAO C.output (edge e.1 e.2) (onlyL e.2) hag C.output Relation.ReflTransGen.refl
      change circuitFun n C (edge e.1 e.2) = circuitFun n C (onlyL e.2) at heq
      rw [(hET e he).2, hsound_l e.2] at heq
      cases heq
    have hreach_l : ∀ l ∈ ET.image Prod.snd, reach (N + l.val) := by
      intro l hl
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      by_contra hnr
      have hag : ∀ i : Fin n, reach i.val → edge e.1 e.2 i = onlyP e.1 i := by
        intro i hri
        have hne : i ≠ Fin.natAdd N e.2 := by
          intro heq
          have hv := congrArg Fin.val heq; simp at hv
          exact hnr (by simpa [hv, Nat.add_comm] using hri)
        simp only [edge, onlyP, hne, or_false]
      have heq := eval_eq_of_cone hAO C.output (edge e.1 e.2) (onlyP e.1) hag C.output Relation.ReflTransGen.refl
      change circuitFun n C (edge e.1 e.2) = circuitFun n C (onlyP e.1) at heq
      rw [(hET e he).2, hsound_p e.1] at heq
      cases heq
    let PT := ET.image Prod.fst
    let LT := ET.image Prod.snd
    let SP := PT.image (fun p : Fin N => p.val)
    let SL := LT.image (fun l : Fin N => N + l.val)
    let SG := R'.image (fun j : Fin C.size => n + j.val)
    have hPT_sub : SP ⊆ Sread := by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact hreach_in_Sread p.val (hreach_p p hp) (by have := p.isLt; omega)
    have hLT_sub : SL ⊆ Sread := by
      intro w hw
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
      exact hreach_in_Sread (N + l.val) (hreach_l l hl) (by have := l.isLt; omega)
    have hdisj_PL : Disjoint SP SL := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw1
      obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hw2
      have := p.isLt; omega
    have hdisj_PLG : Disjoint (SP ∪ SL) SG := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw2
      rcases Finset.mem_union.mp hw1 with h | h
      · obtain ⟨p, _, heq⟩ := Finset.mem_image.mp h
        have := p.isLt; omega
      · obtain ⟨l, _, heq⟩ := Finset.mem_image.mp h
        have := l.isLt; omega
    have hsum_le : PT.card + LT.card + R'.card ≤ Sread.card := by
      have hSP : SP.card = PT.card := Finset.card_image_of_injective _ (fun _ _ h => Fin.ext h)
      have hSL : SL.card = LT.card := Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega))
      have hSG : SG.card = R'.card := Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega))
      have hsubU : (SP ∪ SL) ∪ SG ⊆ Sread := Finset.union_subset (Finset.union_subset hPT_sub hLT_sub) hR'_sub'
      have hc := Finset.card_le_card hsubU
      rw [Finset.card_union_of_disjoint hdisj_PLG, Finset.card_union_of_disjoint hdisj_PL, hSP, hSL, hSG] at hc
      exact hc
    have hPLB_le : PT.card + LT.card + B ≤ C.size + 1 := by omega
    refine ⟨?_, hPLB_le⟩
    by_cases hB0 : B = 0
    · rw [hB0, Nat.mul_zero, Nat.add_zero]
      have hdeg_le1 : ∀ w ∈ Sread, deg w ≤ 1 := by
        intro w hw
        have hle : deg w - 1 ≤ ∑ v ∈ Sread, (deg v - 1) :=
          Finset.single_le_sum (fun v _ => Nat.zero_le (deg v - 1)) hw
        rw [← hB, hB0] at hle
        omega
      refine tree_bound N I hfour C hAO C.output hout_lt ?_ hsound_p hsound_l ?_ ET ?_
      · intro w hw hrw j₁ j₂ b₁ b₂ hj₁ hj₂ hc₁ hc₂
        have hw_in : w ∈ Sread := by
          refine Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₁⟩, ?_⟩
          rw [List.mem_toFinset, ← hc₁]
          obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₁.isLt).2.1
          fin_cases b₁ <;> simp [hx]
        have hcard1 : deg w ≤ 1 := hdeg_le1 w hw_in
        have hmem1 : (j₁, b₁) ∈ (R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
            (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₁⟩, Finset.mem_univ _⟩, hc₁⟩
        have hmem2 : (j₂, b₂) ∈ (R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
            (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₂⟩, Finset.mem_univ _⟩, hc₂⟩
        have heq := Finset.card_le_one.mp hcard1 (j₁, b₁) hmem1 (j₂, b₂) hmem2
        exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      · intro p l _ _ hacc
        by_contra hno
        have h0 : circuitFun n C (edge p l) = false := by
          apply hsound (edge p l)
          · rw [Fintype.card_subtype]
            have hsub : Finset.univ.filter (fun l' : Fin N => edge p l (Fin.natAdd N l') = true) ⊆ {l} := by
              intro l' hl'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, edge, decide_eq_true_eq,
                Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl'
              rcases hl' with h1 | h2
              · have := p.isLt; omega
              · exact Finset.mem_singleton.mpr (Fin.ext (by omega))
            exact (Finset.card_le_card hsub).trans (by simp; omega)
          · rintro ⟨p', l', hi, hp', hl'⟩
            simp only [edge, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp' hl'
            rcases hp' with h1 | h2
            · rcases hl' with h3 | h4
              · have := p'.isLt; omega
              · have hp_eq : p' = p := Fin.ext h1
                have hl_eq : l' = l := Fin.ext (by omega)
                exact hno (hp_eq ▸ hl_eq ▸ hi)
            · have := l.isLt; omega
        change circuitFun n C (edge p l) = true at hacc
        rw [h0] at hacc; cases hacc
      · intro e he
        exact ⟨hreach_p e.1 (Finset.mem_image_of_mem _ he),
          hreach_l e.2 (Finset.mem_image_of_mem _ he), (hET e he).2⟩
    · -- B > 0 case
      have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      let Bwires := Sread.filter fun w => 2 ≤ deg w
      have hBw_ne : Bwires.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hzero : ∑ w ∈ Sread, (deg w - 1) = 0 := by
          apply Finset.sum_eq_zero
          intro w hw
          have hnot : w ∉ Bwires := by rw [hemp]; simp
          simp only [Bwires, Finset.mem_filter, hw, true_and, not_le] at hnot
          omega
        omega
      let w₀ := Bwires.min' hBw_ne
      have hw₀_mem : w₀ ∈ Bwires := Finset.min'_mem Bwires hBw_ne
      have hw₀_S : w₀ ∈ Sread := (Finset.mem_filter.mp hw₀_mem).1
      have hw₀_deg : 2 ≤ deg w₀ := (Finset.mem_filter.mp hw₀_mem).2
      have hw₀_min : ∀ w ∈ Sread, w < w₀ → deg w ≤ 1 := by
        intro w hw hlt
        by_contra h2
        push Not at h2
        have hle := Finset.min'_le Bwires w (Finset.mem_filter.mpr ⟨hw, h2⟩)
        omega
      have hw₀_lt_out : w₀ < C.output := by
        obtain ⟨j, hjR, hwj⟩ := Finset.mem_biUnion.mp hw₀_S
        rw [List.mem_toFinset] at hwj
        have h1 : w₀ < n + j.val := (ao2_gate_inputs hAO j.isLt).2.2 w₀ hwj
        have h2 : n + j.val ≤ C.output := cone_le hAO (Finset.mem_filter.mp hjR).2
        omega
      have hw₀_lt : w₀ < n + C.gates.length := by omega
      obtain ⟨gs, emits, mp, helen, hsz_le, hao, hrb, hemit, hw₀_none, hmp_info, heval⟩ :=
        simplify_wire n C hAO w₀ hw₀_lt
      let ET' := ET.filter fun e => (evalForcedW C n w₀ false (edge e.1 e.2)).getD C.output false = true
      let ET_lost := ET \ ET'
      have hET_part : ET.card = ET'.card + ET_lost.card := by
        have hdisj : Disjoint ET' ET_lost := disjoint_sdiff_self_right
        have hunion : ET' ∪ ET_lost = ET := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
        rw [← hunion, Finset.card_union_of_disjoint hdisj]
      have hET'_bound : ∀ (hmp_out : mp C.output = none), ET' = ∅ := by
        intro hmp_out
        ext e
        simp only [ET', Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ hf
        rw [heval (edge e.1 e.2) C.output hout_lt, hmp_out] at hf
        cases hf
      have hET'_rec : ∀ o', mp C.output = some o' →
          ET'.card ≤ (ET'.image Prod.fst).card + (ET'.image Prod.snd).card + (q + 1) * (B - 1) := by
        intro o' ho'
        let C' : Circuit := ⟨gs, o'⟩
        have hC'_ao : IsAO2 n C' := by
          refine ⟨fun g hg => (hao g hg).1, ?_, fun g hg => (hao g hg).2⟩
          intro j hj i hi
          change i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs at hi
          exact hrb j hj i hi
        have hC'_eval : ∀ z : Fin n → Bool, circuitFun n C' z = (evalForcedW C n w₀ false z).getD C.output false := by
          intro z
          change (runW gs (List.ofFn z)).getD o' false = _
          rw [heval z C.output hout_lt, ho']
        have hC'_sound : ∀ z : Fin n → Bool,
            Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
            (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
            circuitFun n C' z = false := by
          intro z hz hno
          rw [hC'_eval z]
          cases hf : (evalForcedW C n w₀ false z).getD C.output false
          · rfl
          · have hc := evalForcedW_false_le hAO w₀ z C.output hf
            change circuitFun n C z = true at hc
            rw [hsound z hz hno] at hc
            cases hc
        have hC'_ET : ∀ e ∈ ET', I e.1 e.2 ∧ circuitFun n C' (edge e.1 e.2) = true := by
          intro e he
          have hm := Finset.mem_filter.mp he
          exact ⟨(hET e hm.1).1, by rw [hC'_eval]; exact hm.2⟩
        let reach' : ℕ → Prop := fun a => Relation.ReflTransGen (stepR C' n) a C'.output
        let R_c' : Finset (Fin C'.size) := Finset.univ.filter fun j => reach' (n + j.val)
        let Sread' : Finset ℕ := R_c'.biUnion fun j => (C'.gates[j.val]'j.isLt).inputs.toFinset
        let deg' : ℕ → ℕ := fun w =>
          ((R_c' ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
            (C'.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w).card
        let B' : ℕ := ∑ w ∈ Sread', (deg' w - 1)
        -- Prove B' + 1 ≤ B
        have hR_map : ∀ j' ∈ R_c', emits.getD j'.val 0 < C.gates.length ∧
            (⟨emits.getD j'.val 0, (hemit j'.val j'.isLt).1⟩ : Fin C.size) ∈ R := by
          intro j' hj'
          have hj'_reach : reach' (n + j'.val) := (Finset.mem_filter.mp hj').2
          have hlift : ∀ w', reach' w' → ∃ w, w < n + C.gates.length ∧ mp w = some w' ∧ reach w := by
            intro w' hw'
            induction hw' using Relation.ReflTransGen.head_induction_on with
            | refl => exact ⟨C.output, hout_lt, ho', Relation.ReflTransGen.refl⟩
            | head hs' _ ih' =>
              obtain ⟨j₁, rfl, hin₁⟩ := hs'
              obtain ⟨w₁, hw₁_lt, hmp₁, hr₁⟩ := ih'
              have h1 := (hmp_info w₁ hw₁_lt (n + j₁.val) hmp₁).2.2
              have hnotlt : ¬ n + j₁.val < n := by omega
              rw [if_neg hnotlt, show n + j₁.val - n = j₁.val by omega] at h1
              obtain ⟨hj₁_lt, _, _, a₁, b₁, a₁', b₁', hinp₁, hma₁, hmb₁, hgs₁⟩ := hemit j₁.val j₁.isLt
              have hgs₁' : C'.gates[j₁.val]'j₁.isLt = gs.getD j₁.val ⟨GateOp.or, []⟩ :=
                (List.getD_eq_getElem gs _ j₁.isLt).symm
              rw [hgs₁', hgs₁] at hin₁
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hin₁
              let ek : Fin C.size := ⟨emits.getD j₁.val 0, hj₁_lt⟩
              have hek_reach : reach (n + ek.val) := Relation.ReflTransGen.trans h1 hr₁
              rcases hin₁ with rfl | rfl
              · have ha₁_lt : a₁ < n + C.gates.length := by
                  have := (ao2_gate_inputs hAO hj₁_lt).2.2 a₁ (by rw [hinp₁]; simp)
                  omega
                exact ⟨a₁, ha₁_lt, hma₁, Relation.ReflTransGen.head ⟨ek, rfl, by
                  change a₁ ∈ (C.gates[emits.getD j₁.val 0]'hj₁_lt).inputs; rw [hinp₁]; simp⟩ hek_reach⟩
              · have hb₁_lt : b₁ < n + C.gates.length := by
                  have := (ao2_gate_inputs hAO hj₁_lt).2.2 b₁ (by rw [hinp₁]; simp)
                  omega
                exact ⟨b₁, hb₁_lt, hmb₁, Relation.ReflTransGen.head ⟨ek, rfl, by
                  change b₁ ∈ (C.gates[emits.getD j₁.val 0]'hj₁_lt).inputs; rw [hinp₁]; simp⟩ hek_reach⟩
          obtain ⟨w₁, hw₁_lt, hmp₁, hr₁⟩ := hlift (n + j'.val) hj'_reach
          have h1 := (hmp_info w₁ hw₁_lt (n + j'.val) hmp₁).2.2
          have hnotlt : ¬ n + j'.val < n := by omega
          rw [if_neg hnotlt, show n + j'.val - n = j'.val by omega] at h1
          have hj_lt := (hemit j'.val j'.isLt).1
          exact ⟨hj_lt, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.trans h1 hr₁⟩⟩
        have hemit_inj : ∀ j₁ j₂ : Fin C'.size, emits.getD j₁.val 0 = emits.getD j₂.val 0 → j₁ = j₂ := by
          intro j₁ j₂ heq
          have h1 := (hemit j₁.val j₁.isLt).2.1
          have h2 := (hemit j₂.val j₂.isLt).2.1
          rw [heq, h2] at h1
          exact Fin.ext (by have := Option.some.inj h1; omega)
        have hB'_le : B' + (deg w₀ - 1) ≤ B := by
          let F : ℕ → Finset ℕ := fun w' => Sread.filter fun w => mp w = some w'
          have hF_disj : Set.PairwiseDisjoint (↑Sread') F := by
            intro w₁ _ w₂ _ hne
            rw [Function.onFun, Finset.disjoint_left]
            intro w hw1 hw2
            have e1 := (Finset.mem_filter.mp hw1).2
            have e2 := (Finset.mem_filter.mp hw2).2
            exact hne (Option.some.inj (e1.symm.trans e2))
          have hF_sub : Sread'.biUnion F ⊆ Sread.erase w₀ := by
            intro w hw
            obtain ⟨w', _, hmw⟩ := Finset.mem_biUnion.mp hw
            obtain ⟨hwS, hmpw⟩ := Finset.mem_filter.mp hmw
            refine Finset.mem_erase.mpr ⟨?_, hwS⟩
            intro heq
            rw [heq, hw₀_none] at hmpw
            cases hmpw
          have hfiber : ∀ w' ∈ Sread', deg' w' - 1 ≤ ∑ w ∈ F w', (deg w - 1) := by
            intro w' hw'
            let Byp := (F w').filter fun w => n ≤ w ∧ ∀ j' < gs.length, w ≠ n + emits.getD j' 0
            have hF_le_Byp : (F w').card ≤ 1 + Byp.card := by
              have hsub_sdiff : (F w' \ Byp).card ≤ 1 := by
                rw [Finset.card_le_one]
                intro w₁ hw₁ w₂ hw₂
                rw [Finset.mem_sdiff] at hw₁ hw₂
                have hw₁S := (Finset.mem_filter.mp hw₁.1).1
                have hw₁mp := (Finset.mem_filter.mp hw₁.1).2
                have hw₂S := (Finset.mem_filter.mp hw₂.1).1
                have hw₂mp := (Finset.mem_filter.mp hw₂.1).2
                have hw₁_lt : w₁ < n + C.gates.length := by
                  obtain ⟨j, _, hwj⟩ := Finset.mem_biUnion.mp hw₁S
                  rw [List.mem_toFinset] at hwj
                  have hj_len : j.val < C.gates.length := j.isLt
                  have := (ao2_gate_inputs hAO hj_len).2.2 w₁ hwj
                  omega
                have hw₂_lt : w₂ < n + C.gates.length := by
                  obtain ⟨j, _, hwj⟩ := Finset.mem_biUnion.mp hw₂S
                  rw [List.mem_toFinset] at hwj
                  have hj_len : j.val < C.gates.length := j.isLt
                  have := (ao2_gate_inputs hAO hj_len).2.2 w₂ hwj
                  omega
                have hinfo₁ := (hmp_info w₁ hw₁_lt w' hw₁mp).2.1
                have hinfo₂ := (hmp_info w₂ hw₂_lt w' hw₂mp).2.1
                rcases hinfo₁ with ⟨h1n, h1eq⟩ | ⟨j₁, hj₁, h1eq, hw'1⟩ | ⟨j₁, hj₁, hw1j, _, _, hnoem₁, _⟩
                · rcases hinfo₂ with ⟨h2n, h2eq⟩ | ⟨j₂, hj₂, h2eq, hw'2⟩ | ⟨j₂, hj₂, hw2j, _, _, hnoem₂, _⟩
                  · omega
                  · exfalso; have : w₁ = n + j₂ := h1eq.symm.trans hw'2; omega
                  · exfalso; exact hw₂.2 (Finset.mem_filter.mpr ⟨hw₂.1, by omega, fun j' hj' => by
                      have := hnoem₂ j' hj'; omega⟩)
                · rcases hinfo₂ with ⟨h2n, h2eq⟩ | ⟨j₂, hj₂, h2eq, hw'2⟩ | ⟨j₂, hj₂, hw2j, _, _, hnoem₂, _⟩
                  · exfalso; have : w₂ = n + j₁ := h2eq.symm.trans hw'1; omega
                  · have : j₁ = j₂ := by omega
                    rw [h1eq, h2eq, this]
                  · exfalso; exact hw₂.2 (Finset.mem_filter.mpr ⟨hw₂.1, by omega, fun j' hj' => by
                      have := hnoem₂ j' hj'; omega⟩)
                · exfalso; exact hw₁.2 (Finset.mem_filter.mpr ⟨hw₁.1, by omega, fun j' hj' => by
                    have := hnoem₁ j' hj'; omega⟩)
              have hsub_byp : Byp ⊆ F w' := Finset.filter_subset _ _
              have hc := Finset.card_sdiff_add_card_eq_card hsub_byp
              omega
            -- Now show deg' w' + Byp.card ≤ ∑ w ∈ F w', deg w
            let S1 := (R_c' ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
              (C'.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w'
            have hS1_card : S1.card = deg' w' := rfl
            let map1 : Fin C'.size × Fin 2 → Fin C.size × Fin 2 := fun jb =>
              (⟨emits.getD jb.1.val 0, (hemit jb.1.val jb.1.isLt).1⟩, jb.2)
            let S_target := (R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
              (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 ∈ F w'
            have hS_target_card : S_target.card = ∑ w ∈ F w', deg w := by
              rw [← Finset.card_biUnion]
              · congr 1
                ext ⟨j, c⟩
                simp only [S_target, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product,
                  Finset.mem_univ, and_true]
                constructor
                · rintro ⟨hjR, hwF⟩; exact ⟨_, hwF, hjR, rfl⟩
                · rintro ⟨w, hwF, hjR, rfl⟩; exact ⟨hjR, hwF⟩
              · intro w₁ _ w₂ _ hne
                rw [Function.onFun, Finset.disjoint_left]
                intro ⟨j, c⟩ h1 h2
                exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
            have hmap1_mem : ∀ jb ∈ S1, map1 jb ∈ S_target := by
              intro ⟨j', c⟩ hjb
              obtain ⟨hprod, hc⟩ := Finset.mem_filter.mp hjb
              have hj'R : j' ∈ R_c' := (Finset.mem_product.mp hprod).1
              have hjR := (hR_map j' hj'R).2
              obtain ⟨hj_lt, _, _, a₁, b₁, a₁', b₁', hinp₁, hma₁, hmb₁, hgs₁⟩ := hemit j'.val j'.isLt
              have hgs₁' : C'.gates[j'.val]'j'.isLt = gs.getD j'.val ⟨GateOp.or, []⟩ :=
                (List.getD_eq_getElem gs _ j'.isLt).symm
              change (C'.gates[j'.val]'j'.isLt).inputs.getD c.val 0 = w' at hc
              rw [hgs₁', hgs₁] at hc
              refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hjR, Finset.mem_univ _⟩, ?_⟩
              fin_cases c
              · change (C.gates[emits.getD j'.val 0]'hj_lt).inputs.getD 0 0 ∈ F w'
                rw [hinp₁]
                simp only [List.getD_cons_zero]
                simp only [List.getD_cons_zero] at hc
                rw [← hc]
                refine Finset.mem_filter.mpr ⟨?_, hma₁⟩
                exact Finset.mem_biUnion.mpr ⟨⟨emits.getD j'.val 0, hj_lt⟩, hjR,
                  List.mem_toFinset.mpr (by change a₁ ∈ (C.gates[emits.getD j'.val 0]'hj_lt).inputs; rw [hinp₁]; simp)⟩
              · change (C.gates[emits.getD j'.val 0]'hj_lt).inputs.getD 1 0 ∈ F w'
                rw [hinp₁]
                simp only [List.getD_cons_succ, List.getD_cons_zero]
                simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
                rw [← hc]
                refine Finset.mem_filter.mpr ⟨?_, hmb₁⟩
                exact Finset.mem_biUnion.mpr ⟨⟨emits.getD j'.val 0, hj_lt⟩, hjR,
                  List.mem_toFinset.mpr (by change b₁ ∈ (C.gates[emits.getD j'.val 0]'hj_lt).inputs; rw [hinp₁]; simp)⟩
            have hmap1_inj : Set.InjOn map1 S1 := by
              intro ⟨j₁, c₁⟩ _ ⟨j₂, c₂⟩ _ heq
              have hj := congrArg (fun p : Fin C.size × Fin 2 => p.1.val) heq
              have hc := congrArg Prod.snd heq
              dsimp only [map1] at hj hc
              exact Prod.ext (hemit_inj j₁ j₂ hj) hc
            have hByp_map : ∀ w ∈ Byp, ∃ jb ∈ S_target, jb.1.val = w - n ∧ ∀ jb' ∈ S1, map1 jb' ≠ jb := by
              intro w hw
              obtain ⟨hwF, hwn, hnoem⟩ := Finset.mem_filter.mp hw
              obtain ⟨hwS, hwmp⟩ := Finset.mem_filter.mp hwF
              obtain ⟨j_out, hj_outR, hw_in⟩ := Finset.mem_biUnion.mp hwS
              rw [List.mem_toFinset] at hw_in
              have hw_lt : w < n + C.gates.length := by
                have hj_len : j_out.val < C.gates.length := j_out.isLt
                have := (ao2_gate_inputs hAO hj_len).2.2 w hw_in
                omega
              have hw_reach : reach w := Relation.ReflTransGen.head ⟨j_out, rfl, hw_in⟩ (Finset.mem_filter.mp hj_outR).2
              have hinfo := (hmp_info w hw_lt w' hwmp).2.1
              rcases hinfo with ⟨h1, _⟩ | ⟨j', hj', heq, _⟩ | ⟨j, hjC, heq, _, _, _, c, hc⟩
              · omega
              · exfalso; exact hnoem j' hj' heq
              · have hj_eq : j = w - n := by omega
                have hjR : (⟨j, hjC⟩ : Fin C.size) ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (by omega : n + j = w) ▸ hw_reach⟩
                refine ⟨(⟨j, hjC⟩, c), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hjR, Finset.mem_univ _⟩, ?_⟩,
                    hj_eq, ?_⟩
                · refine Finset.mem_filter.mpr ⟨?_, hc⟩
                  refine Finset.mem_biUnion.mpr ⟨⟨j, hjC⟩, hjR, List.mem_toFinset.mpr ?_⟩
                  obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO hjC).2.1
                  have hmem : (C.gates[j]'hjC).inputs.getD c.val 0 ∈ (C.gates[j]'hjC).inputs := by
                    fin_cases c <;> simp [hx]
                  exact hmem
                · rintro ⟨j', c'⟩ _ hcontra
                  have h1 := congrArg (fun p : Fin C.size × Fin 2 => p.1.val) hcontra
                  dsimp only [map1] at h1
                  exact hnoem j'.val j'.isLt (by omega)
            -- Build Finset S2 ⊆ S_target \ (S1.image map1) of card ≥ Byp.card
            let S2 := S_target.filter fun jb => (n + jb.1.val) ∈ Byp
            have hS2_disj : Disjoint (S1.image map1) S2 := by
              rw [Finset.disjoint_left]
              intro jb h1 h2
              obtain ⟨⟨j', c'⟩, _, rfl⟩ := Finset.mem_image.mp h1
              have hb := (Finset.mem_filter.mp h2).2
              have hnoem := (Finset.mem_filter.mp hb).2.2
              exact hnoem j'.val j'.isLt rfl
            have hByp_le_S2 : Byp.card ≤ S2.card := by
              have himg : Byp ⊆ S2.image (fun jb => n + jb.1.val) := by
                intro w hw
                obtain ⟨jb, hjb_t, hjb_eq, _⟩ := hByp_map w hw
                refine Finset.mem_image.mpr ⟨jb, Finset.mem_filter.mpr ⟨hjb_t, ?_⟩, ?_⟩
                · have hwn := (Finset.mem_filter.mp hw).2.1
                  have : n + jb.1.val = w := by omega
                  rw [this]; exact hw
                · have hwn := (Finset.mem_filter.mp hw).2.1
                  omega
              exact (Finset.card_le_card himg).trans Finset.card_image_le
            have hS1S2_le : (S1.image map1).card + S2.card ≤ S_target.card := by
              rw [← Finset.card_union_of_disjoint hS2_disj]
              exact Finset.card_le_card (Finset.union_subset
                (Finset.image_subset_iff.mpr hmap1_mem) (Finset.filter_subset _ _))
            have hS1_eq : (S1.image map1).card = deg' w' := by
              rw [Finset.card_image_of_injOn hmap1_inj, hS1_card]
            have hsum_deg_F : ∑ w ∈ F w', deg w = S_target.card := hS_target_card.symm
            have hdeg'_pos : 1 ≤ deg' w' := by
              obtain ⟨j', hj'R, hwj'⟩ := Finset.mem_biUnion.mp hw'
              rw [List.mem_toFinset] at hwj'
              obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (ao2_gate_inputs hC'_ao j'.isLt).2.1
              rw [hab] at hwj'
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hwj'
              refine Finset.card_pos.mpr ?_
              rcases hwj' with rfl | rfl
              · exact ⟨(j', 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hj'R, Finset.mem_univ _⟩, by simp [hab]⟩⟩
              · exact ⟨(j', 1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hj'R, Finset.mem_univ _⟩, by simp [hab]⟩⟩
            have hF_sum_ge : (F w').card ≤ ∑ w ∈ F w', deg w := by
              calc (F w').card = ∑ _w ∈ F w', 1 := by simp
                _ ≤ ∑ w ∈ F w', deg w := Finset.sum_le_sum (fun w hw => hdeg_pos w (Finset.mem_filter.mp hw).1)
            have hsum_sub : ∑ w ∈ F w', (deg w - 1) + (F w').card = ∑ w ∈ F w', deg w := by
              calc ∑ w ∈ F w', (deg w - 1) + (F w').card
                  = ∑ w ∈ F w', ((deg w - 1) + 1) := by rw [Finset.sum_add_distrib]; simp
                _ = ∑ w ∈ F w', deg w := Finset.sum_congr rfl (fun w hw => by
                    have := hdeg_pos w (Finset.mem_filter.mp hw).1; omega)
            omega
          calc B' + (deg w₀ - 1)
              ≤ (∑ w' ∈ Sread', ∑ w ∈ F w', (deg w - 1)) + (deg w₀ - 1) :=
                Nat.add_le_add_right (Finset.sum_le_sum hfiber) _
            _ = (∑ w ∈ Sread'.biUnion F, (deg w - 1)) + (deg w₀ - 1) := by
                rw [Finset.sum_biUnion hF_disj]
            _ ≤ (∑ w ∈ Sread.erase w₀, (deg w - 1)) + (deg w₀ - 1) :=
                Nat.add_le_add_right (Finset.sum_le_sum_of_subset_of_nonneg hF_sub (fun _ _ _ => Nat.zero_le _)) _
            _ = ∑ w ∈ Sread, (deg w - 1) := by
                rw [Nat.add_comm, Finset.add_sum_erase Sread (fun w => deg w - 1) hw₀_S]
            _ = B := hB.symm
        have hB'_lt : B' < B := by omega
        have hrec := ih B' hB'_lt C' hC'_ao hC'_sound ET' hC'_ET rfl
        calc ET'.card ≤ (ET'.image Prod.fst).card + (ET'.image Prod.snd).card + (q + 1) * B' := hrec.1
          _ ≤ (ET'.image Prod.fst).card + (ET'.image Prod.snd).card + (q + 1) * (B - 1) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      -- Helper to combine ET' and ET_lost when ET_lost.card ≤ q + 1
      have hcombine_small : ET_lost.card ≤ q + 1 →
          ET.card ≤ PT.card + LT.card + (q + 1) * B := by
        intro hlost
        by_cases hmp_out : mp C.output = none
        · have heq := hET'_bound hmp_out
          have hlost_eq : ET_lost = ET := by simp [ET_lost, heq]
          rw [hlost_eq] at hlost
          have hB1 : 1 ≤ B := hBpos
          calc ET.card ≤ q + 1 := hlost
            _ ≤ PT.card + LT.card + (q + 1) * 1 := by omega
            _ ≤ PT.card + LT.card + (q + 1) * B :=
              Nat.add_le_add_left (Nat.mul_le_mul_left _ hB1) _
        · obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.mp hmp_out
          have hrec := hET'_rec o' ho'
          have hsubP : ET'.image Prod.fst ⊆ PT := Finset.image_subset_image (Finset.filter_subset _ _)
          have hsubL : ET'.image Prod.snd ⊆ LT := Finset.image_subset_image (Finset.filter_subset _ _)
          have hP' : (ET'.image Prod.fst).card ≤ PT.card := Finset.card_le_card hsubP
          have hL' : (ET'.image Prod.snd).card ≤ LT.card := Finset.card_le_card hsubL
          have hq1 : (q + 1) * (B - 1) + (q + 1) = (q + 1) * B := by
            have : (B - 1) + 1 = B := Nat.sub_add_cancel hBpos
            calc (q + 1) * (B - 1) + (q + 1) = (q + 1) * ((B - 1) + 1) := by ring
              _ = (q + 1) * B := by rw [this]
          omega
      -- Now bound ET_lost!
      by_cases hw₀_in : w₀ < n
      · apply hcombine_small
        by_cases hw₀_P : w₀ < N
        · have hsub : ET_lost ⊆ (Finset.univ.filter fun l : Fin N => I ⟨w₀, hw₀_P⟩ l).image
              (fun l => (⟨w₀, hw₀_P⟩, l)) := by
            intro e he
            rw [Finset.mem_sdiff] at he
            have heET := he.1
            have he_n := he.2
            simp only [ET', Finset.mem_filter, heET, true_and] at he_n
            have hne : e.1 = ⟨w₀, hw₀_P⟩ := by
              by_contra hne_p
              have hf : (evalForcedW C n w₀ false (edge e.1 e.2)).getD C.output false =
                  (C.wires (List.ofFn (edge e.1 e.2))).getD C.output false := by
                rw [evalForcedW_eq_of_input hAO w₀ hw₀_in]
                congr 3
                funext i
                by_cases hi : i.val = w₀
                · simp only [hi, ↓reduceIte]
                  symm
                  simp only [edge, decide_eq_false_iff_not, not_or]
                  exact ⟨fun h => hne_p (Fin.ext (by have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; dsimp only; omega)),
                         fun h => by have := e.2.isLt; have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; omega⟩
                · simp [hi]
              rw [hf] at he_n
              exact he_n (hET e heET).2
            refine Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [← hne]; exact (hET e heET).1
            · exact Prod.ext hne.symm rfl
          calc ET_lost.card ≤ ((Finset.univ.filter fun l : Fin N => I ⟨w₀, hw₀_P⟩ l).image
                (fun l => (⟨w₀, hw₀_P⟩, l))).card := Finset.card_le_card hsub
            _ ≤ (Finset.univ.filter fun l : Fin N => I ⟨w₀, hw₀_P⟩ l).card := Finset.card_image_le
            _ = q + 1 := by simpa [Fintype.card_subtype] using hrow ⟨w₀, hw₀_P⟩
        · have hsub : ET_lost ⊆ (Finset.univ.filter fun p : Fin N => I p ⟨w₀ - N, by omega⟩).image
              (fun p => (p, ⟨w₀ - N, by omega⟩)) := by
            intro e he
            rw [Finset.mem_sdiff] at he
            have heET := he.1
            have he_n := he.2
            simp only [ET', Finset.mem_filter, heET, true_and] at he_n
            have hne : e.2 = ⟨w₀ - N, by omega⟩ := by
              by_contra hne_l
              have hf : (evalForcedW C n w₀ false (edge e.1 e.2)).getD C.output false =
                  (C.wires (List.ofFn (edge e.1 e.2))).getD C.output false := by
                rw [evalForcedW_eq_of_input hAO w₀ hw₀_in]
                congr 3
                funext i
                by_cases hi : i.val = w₀
                · simp only [hi, ↓reduceIte]
                  symm
                  simp only [edge, decide_eq_false_iff_not, not_or]
                  exact ⟨fun h => by have := e.1.isLt; have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; omega,
                         fun h => hne_l (Fin.ext (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; dsimp only; omega))⟩
                · simp [hi]
              rw [hf] at he_n
              exact he_n (hET e heET).2
            refine Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [← hne]; exact (hET e heET).1
            · exact Prod.ext rfl hne.symm
          calc ET_lost.card ≤ ((Finset.univ.filter fun p : Fin N => I p ⟨w₀ - N, by omega⟩).image
                (fun p => (p, ⟨w₀ - N, by omega⟩))).card := Finset.card_le_card hsub
            _ ≤ (Finset.univ.filter fun p : Fin N => I p ⟨w₀ - N, by omega⟩).card := Finset.card_image_le
            _ = q + 1 := by simpa [Fintype.card_subtype] using hcol ⟨w₀ - N, by omega⟩
      · -- Internal gate w₀ (n ≤ w₀)
        have hw₀_ge : n ≤ w₀ := by omega
        let cone_w₀ : ℕ → Prop := fun v => Relation.ReflTransGen (stepR C n) v w₀
        have hw₀_reach : reach w₀ := by
          obtain ⟨j, hjR, hwj⟩ := Finset.mem_biUnion.mp hw₀_S
          rw [List.mem_toFinset] at hwj
          exact Relation.ReflTransGen.head ⟨j, rfl, hwj⟩ (Finset.mem_filter.mp hjR).2
        have hreach_step : ∀ j : Fin C.size, reach (n + j.val) → ∀ a ∈ (C.gates[j.val]'j.isLt).inputs, reach a := by
          intro j hj a ha
          exact Relation.ReflTransGen.head ⟨j, rfl, ha⟩ hj
        have huniq_cone : ∀ w < w₀, cone_w₀ w →
            ∀ j₁ j₂ : Fin C.size, reach (n + j₁.val) → reach (n + j₂.val) →
            w ∈ (C.gates[j₁.val]'j₁.isLt).inputs → w ∈ (C.gates[j₂.val]'j₂.isLt).inputs → j₁ = j₂ := by
          intro w hwl _ j₁ j₂ hj₁ hj₂ hin₁ hin₂
          have hwS : w ∈ Sread := Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₁⟩,
            List.mem_toFinset.mpr hin₁⟩
          have hdeg1 : deg w ≤ 1 := hw₀_min w hwS hwl
          obtain ⟨c₁, hc₁⟩ : ∃ c₁ : Fin 2, (C.gates[j₁.val]'j₁.isLt).inputs.getD c₁.val 0 = w := by
            obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₁.isLt).2.1
            have hm := hin₁; rw [hx] at hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with rfl | rfl
            · exact ⟨0, by change (C.gates[j₁.val]'j₁.isLt).inputs.getD 0 0 = w; rw [hx]; rfl⟩
            · exact ⟨1, by change (C.gates[j₁.val]'j₁.isLt).inputs.getD 1 0 = w; rw [hx]; rfl⟩
          obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Fin 2, (C.gates[j₂.val]'j₂.isLt).inputs.getD c₂.val 0 = w := by
            obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₂.isLt).2.1
            have hm := hin₂; rw [hx] at hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with rfl | rfl
            · exact ⟨0, by change (C.gates[j₂.val]'j₂.isLt).inputs.getD 0 0 = w; rw [hx]; rfl⟩
            · exact ⟨1, by change (C.gates[j₂.val]'j₂.isLt).inputs.getD 1 0 = w; rw [hx]; rfl⟩
          have hmem1 : (j₁, c₁) ∈ (R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
              (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w :=
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₁⟩, Finset.mem_univ _⟩, hc₁⟩
          have hmem2 : (j₂, c₂) ∈ (R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
              (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w :=
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₂⟩, Finset.mem_univ _⟩, hc₂⟩
          exact congrArg Prod.fst (Finset.card_le_one.mp hdeg1 (j₁, c₁) hmem1 (j₂, c₂) hmem2)
        have hout_nc : ¬ cone_w₀ C.output := by
          intro hc
          have := cone_le hAO hc
          omega
        let outOf : (Fin n → Bool) → (Fin n → Bool) := fun z i => if cone_w₀ i.val then false else z i
        have heq_out : ∀ z : Fin n → Bool,
            (C.wires (List.ofFn z)).getD C.output false =
              (evalForcedW C n w₀ ((C.wires (List.ofFn z)).getD w₀ false) (outOf z)).getD C.output false := by
          intro z
          exact eval_eq_forced_outside_cone hAO w₀ hw₀_ge reach hreach_step huniq_cone hw₀_reach
            z (outOf z) (fun i hi => by dsimp only [outOf]; rw [if_neg hi]) C.output Relation.ReflTransGen.refl hout_nc
        have heq_forced_out : ∀ z : Fin n → Bool,
            (evalForcedW C n w₀ false z).getD C.output false =
              (evalForcedW C n w₀ false (outOf z)).getD C.output false := by
          intro z
          exact forced_false_eq_outside_cone hAO w₀ hw₀_ge reach hreach_step huniq_cone hw₀_reach
            z (outOf z) (fun i hi => by dsimp only [outOf]; rw [if_neg hi]) C.output Relation.ReflTransGen.refl hout_nc
        have hw₀_true_of_lost : ∀ e ∈ ET_lost, (C.wires (List.ofFn (edge e.1 e.2))).getD w₀ false = true := by
          intro e he
          rw [Finset.mem_sdiff] at he
          have heET := he.1
          have he_n := he.2
          simp only [ET', Finset.mem_filter, heET, true_and] at he_n
          by_contra hnf
          have hwf : (C.wires (List.ofFn (edge e.1 e.2))).getD w₀ false = false := Bool.eq_false_iff.mpr hnf
          have hc := heq_out (edge e.1 e.2)
          rw [hwf] at hc
          have ht : (evalForcedW C n w₀ false (outOf (edge e.1 e.2))).getD C.output false = true := by
            rw [← hc]; exact (hET e heET).2
          have hm := evalForcedW_mono_z hAO w₀ false (outOf (edge e.1 e.2)) (edge e.1 e.2)
            (fun i hi => by simp only [outOf] at hi; split_ifs at hi <;> exact hi) C.output ht
          exact he_n hm
        cases htop0 : (evalForcedW C n w₀ true (fun _ => false)).getD C.output false with
        | true =>
          -- Case 1: g₀ reaches output unconditionally!
          have hgw_p : ∀ p : Fin N, (C.wires (List.ofFn (onlyP p))).getD w₀ false = false := by
            intro p
            by_contra hnf
            have hwt : (C.wires (List.ofFn (onlyP p))).getD w₀ false = true :=
              Bool.eq_true_of_not_eq_false (fun h => hnf h)
            have hc := heq_out (onlyP p)
            rw [hwt] at hc
            have hge := evalForcedW_mono_z hAO w₀ true (fun _ => false) (outOf (onlyP p))
              (fun _ h => by cases h) C.output htop0
            rw [← hc] at hge
            change circuitFun n C (onlyP p) = true at hge
            rw [hsound_p p] at hge; cases hge
          have hgw_l : ∀ l : Fin N, (C.wires (List.ofFn (onlyL l))).getD w₀ false = false := by
            intro l
            by_contra hnf
            have hwt : (C.wires (List.ofFn (onlyL l))).getD w₀ false = true :=
              Bool.eq_true_of_not_eq_false (fun h => hnf h)
            have hc := heq_out (onlyL l)
            rw [hwt] at hc
            have hge := evalForcedW_mono_z hAO w₀ true (fun _ => false) (outOf (onlyL l))
              (fun _ h => by cases h) C.output htop0
            rw [← hc] at hge
            change circuitFun n C (onlyL l) = true at hge
            rw [hsound_l l] at hge; cases hge
          have hlost_cone : ∀ e ∈ ET_lost, cone_w₀ e.1.val ∧ cone_w₀ (N + e.2.val) := by
            intro e he
            have hwt := hw₀_true_of_lost e he
            constructor
            · by_contra hnp
              have heq_l : (C.wires (List.ofFn (edge e.1 e.2))).getD w₀ false =
                  (C.wires (List.ofFn (onlyL e.2))).getD w₀ false := by
                apply eval_eq_of_cone hAO w₀ _ _ _ w₀ Relation.ReflTransGen.refl
                intro i hi
                have hne : i ≠ Fin.castAdd N e.1 := fun h => hnp (by
                  have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; simpa [hv] using hi)
                simp only [edge, onlyL, hne, false_or]
              rw [heq_l, hgw_l e.2] at hwt; cases hwt
            · by_contra hnl
              have heq_p : (C.wires (List.ofFn (edge e.1 e.2))).getD w₀ false =
                  (C.wires (List.ofFn (onlyP e.1))).getD w₀ false := by
                apply eval_eq_of_cone hAO w₀ _ _ _ w₀ Relation.ReflTransGen.refl
                intro i hi
                have hne : i ≠ Fin.natAdd N e.2 := fun h => hnl (by
                  have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hi)
                simp only [edge, onlyP, hne, or_false]
              rw [heq_p, hgw_p e.1] at hwt; cases hwt
          have hET'_disj_P : ∀ e ∈ ET', ¬ cone_w₀ e.1.val := by
            intro e he hcp
            simp only [ET', Finset.mem_filter] at he
            have hfo := heq_forced_out (edge e.1 e.2)
            rw [he.2] at hfo
            have hsub_out : ∀ i : Fin n, outOf (edge e.1 e.2) i = true → onlyL e.2 i = true := by
              intro i hi
              simp only [outOf] at hi
              by_cases hic : cone_w₀ i.val
              · simp [hic] at hi
              · simp only [hic, ↓reduceIte, edge, decide_eq_true_eq] at hi
                rcases hi with h_eq | h_eq
                · exact absurd hcp (by have hv := congrArg Fin.val h_eq; simp only [Fin.val_castAdd] at hv; simpa [hv] using hic)
                · simp [onlyL, h_eq]
            have hm1 := evalForcedW_mono_z hAO w₀ false (outOf (edge e.1 e.2)) (onlyL e.2) hsub_out C.output hfo.symm
            have hm2 := evalForcedW_false_le hAO w₀ (onlyL e.2) C.output hm1
            change circuitFun n C (onlyL e.2) = true at hm2
            rw [hsound_l e.2] at hm2; cases hm2
          have hET'_disj_L : ∀ e ∈ ET', ¬ cone_w₀ (N + e.2.val) := by
            intro e he hcl
            simp only [ET', Finset.mem_filter] at he
            have hfo := heq_forced_out (edge e.1 e.2)
            rw [he.2] at hfo
            have hsub_out : ∀ i : Fin n, outOf (edge e.1 e.2) i = true → onlyP e.1 i = true := by
              intro i hi
              simp only [outOf] at hi
              by_cases hic : cone_w₀ i.val
              · simp [hic] at hi
              · simp only [hic, ↓reduceIte, edge, decide_eq_true_eq] at hi
                rcases hi with h_eq | h_eq
                · simp [onlyP, h_eq]
                · exact absurd hcl (by have hv := congrArg Fin.val h_eq; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hic)
            have hm1 := evalForcedW_mono_z hAO w₀ false (outOf (edge e.1 e.2)) (onlyP e.1) hsub_out C.output hfo.symm
            have hm2 := evalForcedW_false_le hAO w₀ (onlyP e.1) C.output hm1
            change circuitFun n C (onlyP e.1) = true at hm2
            rw [hsound_p e.1] at hm2; cases hm2
          have htree : ET_lost.card ≤ (ET_lost.image Prod.fst).card + (ET_lost.image Prod.snd).card := by
            refine tree_bound N I hfour C hAO w₀ hw₀_lt ?_ hgw_p hgw_l ?_ ET_lost ?_
            · intro w hw hrw j₁ j₂ b₁ b₂ hj₁ hj₂ hc₁ hc₂
              have hw_in : w ∈ Sread := by
                have hj₁R : j₁ ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.trans hj₁ hw₀_reach⟩
                refine Finset.mem_biUnion.mpr ⟨j₁, hj₁R, ?_⟩
                rw [List.mem_toFinset, ← hc₁]
                obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (ao2_gate_inputs hAO j₁.isLt).2.1
                fin_cases b₁ <;> simp [hx]
              have hcard1 : deg w ≤ 1 := hw₀_min w hw_in hw
              have hj₁R : j₁ ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.trans hj₁ hw₀_reach⟩
              have hj₂R : j₂ ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.trans hj₂ hw₀_reach⟩
              have hmem1 : (j₁, b₁) ∈ (R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
                  (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w :=
                Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hj₁R, Finset.mem_univ _⟩, hc₁⟩
              have hmem2 : (j₂, b₂) ∈ (R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
                  (C.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w :=
                Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hj₂R, Finset.mem_univ _⟩, hc₂⟩
              have heq := Finset.card_le_one.mp hcard1 (j₁, b₁) hmem1 (j₂, b₂) hmem2
              exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
            · intro p l hcp hcl hwt
              have hc := heq_out (edge p l)
              rw [hwt] at hc
              have hge := evalForcedW_mono_z hAO w₀ true (fun _ => false) (outOf (edge p l))
                (fun _ h => by cases h) C.output htop0
              rw [← hc] at hge
              by_contra hno
              have h0 : circuitFun n C (edge p l) = false := by
                apply hsound (edge p l)
                · rw [Fintype.card_subtype]
                  have hsub : Finset.univ.filter (fun l' : Fin N => edge p l (Fin.natAdd N l') = true) ⊆ {l} := by
                    intro l' hl'
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and, edge, decide_eq_true_eq,
                      Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl'
                    rcases hl' with h1 | h2
                    · have := p.isLt; omega
                    · exact Finset.mem_singleton.mpr (Fin.ext (by omega))
                  exact (Finset.card_le_card hsub).trans (by simp; omega)
                · rintro ⟨p', l', hi, hp', hl'⟩
                  simp only [edge, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp' hl'
                  rcases hp' with h1 | h2
                  · rcases hl' with h3 | h4
                    · have := p'.isLt; omega
                    · exact hno ((Fin.ext h1 : p' = p) ▸ (Fin.ext (by omega) : l' = l) ▸ hi)
                  · have := l.isLt; omega
              change circuitFun n C (edge p l) = true at hge
              rw [h0] at hge; cases hge
            · intro e he
              exact ⟨(hlost_cone e he).1, (hlost_cone e he).2, hw₀_true_of_lost e he⟩
          have hdisj_P : Disjoint (ET'.image Prod.fst) (ET_lost.image Prod.fst) := by
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp hp1
            obtain ⟨e₂, he₂, heq⟩ := Finset.mem_image.mp hp2
            exact hET'_disj_P e₁ he₁ (heq ▸ (hlost_cone e₂ he₂).1)
          have hdisj_L : Disjoint (ET'.image Prod.snd) (ET_lost.image Prod.snd) := by
            rw [Finset.disjoint_left]
            intro l hl1 hl2
            obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp hl1
            obtain ⟨e₂, he₂, heq⟩ := Finset.mem_image.mp hl2
            exact hET'_disj_L e₁ he₁ (heq ▸ (hlost_cone e₂ he₂).2)
          have hP_sum : (ET'.image Prod.fst).card + (ET_lost.image Prod.fst).card ≤ (ET.image Prod.fst).card := by
            rw [← Finset.card_union_of_disjoint hdisj_P]
            exact Finset.card_le_card (Finset.union_subset
              (Finset.image_subset_image (Finset.filter_subset _ _))
              (Finset.image_subset_image Finset.sdiff_subset))
          have hL_sum : (ET'.image Prod.snd).card + (ET_lost.image Prod.snd).card ≤ (ET.image Prod.snd).card := by
            rw [← Finset.card_union_of_disjoint hdisj_L]
            exact Finset.card_le_card (Finset.union_subset
              (Finset.image_subset_image (Finset.filter_subset _ _))
              (Finset.image_subset_image Finset.sdiff_subset))
          by_cases hmp_out : mp C.output = none
          · have heq := hET'_bound hmp_out
            have hlost_eq : ET_lost = ET := by simp [ET_lost, heq]
            rw [hlost_eq] at htree
            omega
          · obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.mp hmp_out
            have hrec := hET'_rec o' ho'
            have : (q + 1) * (B - 1) ≤ (q + 1) * B := Nat.mul_le_mul_left _ (Nat.sub_le B 1)
            change ET.card ≤ (ET.image Prod.fst).card + (ET.image Prod.snd).card + (q + 1) * B
            omega
        | false =>
          -- Case 2: g₀ cannot reach output alone!
          apply hcombine_small
          have hsplit_lost : ∀ e ∈ ET_lost,
              (cone_w₀ e.1.val ∧ ¬ cone_w₀ (N + e.2.val)) ∨
              (¬ cone_w₀ e.1.val ∧ cone_w₀ (N + e.2.val)) := by
            intro e he
            have hwt := hw₀_true_of_lost e he
            by_cases hcp : cone_w₀ e.1.val <;> by_cases hcl : cone_w₀ (N + e.2.val)
            · exfalso
              have hout0 : outOf (edge e.1 e.2) = fun _ => false := by
                ext i
                simp only [outOf]
                split_ifs with hic
                · rfl
                · simp only [edge, decide_eq_false_iff_not, not_or]
                  exact ⟨fun h => hic (by have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; simpa [hv] using hcp),
                         fun h => hic (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hcl)⟩
              have hc := heq_out (edge e.1 e.2)
              rw [hwt, hout0, htop0] at hc
              have hm := (hET e (Finset.sdiff_subset he)).2
              change (C.wires (List.ofFn (edge e.1 e.2))).getD C.output false = true at hm
              rw [hc] at hm; cases hm
            · exact Or.inl ⟨hcp, hcl⟩
            · exact Or.inr ⟨hcp, hcl⟩
            · exfalso
              have hgw0 : (C.wires (List.ofFn (edge e.1 e.2))).getD w₀ false =
                  (C.wires (List.ofFn (fun _ : Fin n => false))).getD w₀ false := by
                apply eval_eq_of_cone hAO w₀ _ _ _ w₀ Relation.ReflTransGen.refl
                intro i hi
                simp only [edge, decide_eq_false_iff_not, not_or]
                exact ⟨fun h => hcp (by have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; simpa [hv] using hi),
                       fun h => hcl (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hi)⟩
              have hrep : List.ofFn (fun _ : Fin n => false) = List.replicate n false := List.ofFn_const _ _
              rw [hgw0, hrep, isAO2_w0_false hAO w₀] at hwt
              cases hwt
          let ET_p := ET_lost.filter fun e => cone_w₀ e.1.val ∧ ¬ cone_w₀ (N + e.2.val)
          let ET_l := ET_lost.filter fun e => ¬ cone_w₀ e.1.val ∧ cone_w₀ (N + e.2.val)
          have hP_prop : ∀ e ∈ ET_p, (C.wires (List.ofFn (onlyP e.1))).getD w₀ false = true ∧
              (evalForcedW C n w₀ true (onlyL e.2)).getD C.output false = true := by
            intro e he
            have hm := (Finset.mem_filter.mp he).1
            have hpn := (Finset.mem_filter.mp he).2
            have hwt := hw₀_true_of_lost e hm
            have heq_p : (C.wires (List.ofFn (edge e.1 e.2))).getD w₀ false =
                (C.wires (List.ofFn (onlyP e.1))).getD w₀ false := by
              apply eval_eq_of_cone hAO w₀ _ _ _ w₀ Relation.ReflTransGen.refl
              intro i hi
              have hne : i ≠ Fin.natAdd N e.2 := fun h => hpn.2 (by
                have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hi)
              simp only [edge, onlyP, hne, or_false]
            have hc := heq_out (edge e.1 e.2)
            rw [hwt] at hc
            have hacc : (C.wires (List.ofFn (edge e.1 e.2))).getD C.output false = true :=
              (hET e (Finset.sdiff_subset hm)).2
            rw [hc] at hacc
            have hsub_out : ∀ i : Fin n, outOf (edge e.1 e.2) i = true → onlyL e.2 i = true := by
              intro i hi
              simp only [outOf] at hi
              by_cases hic : cone_w₀ i.val
              · simp [hic] at hi
              · simp only [hic, ↓reduceIte, edge, decide_eq_true_eq] at hi
                rcases hi with h_eq | h_eq
                · exact absurd hpn.1 (by have hv := congrArg Fin.val h_eq; simp only [Fin.val_castAdd] at hv; simpa [hv] using hic)
                · simp [onlyL, h_eq]
            exact ⟨heq_p ▸ hwt, evalForcedW_mono_z hAO w₀ true (outOf (edge e.1 e.2)) (onlyL e.2) hsub_out C.output hacc⟩
          have hL_prop : ∀ e ∈ ET_l, (C.wires (List.ofFn (onlyL e.2))).getD w₀ false = true ∧
              (evalForcedW C n w₀ true (onlyP e.1)).getD C.output false = true := by
            intro e he
            have hm := (Finset.mem_filter.mp he).1
            have hln := (Finset.mem_filter.mp he).2
            have hwt := hw₀_true_of_lost e hm
            have heq_l : (C.wires (List.ofFn (edge e.1 e.2))).getD w₀ false =
                (C.wires (List.ofFn (onlyL e.2))).getD w₀ false := by
              apply eval_eq_of_cone hAO w₀ _ _ _ w₀ Relation.ReflTransGen.refl
              intro i hi
              have hne : i ≠ Fin.castAdd N e.1 := fun h => hln.1 (by
                have hv := congrArg Fin.val h; simp only [Fin.val_castAdd] at hv; simpa [hv] using hi)
              simp only [edge, onlyL, hne, false_or]
            have hc := heq_out (edge e.1 e.2)
            rw [hwt] at hc
            have hacc : (C.wires (List.ofFn (edge e.1 e.2))).getD C.output false = true :=
              (hET e (Finset.sdiff_subset hm)).2
            rw [hc] at hacc
            have hsub_out : ∀ i : Fin n, outOf (edge e.1 e.2) i = true → onlyP e.1 i = true := by
              intro i hi
              simp only [outOf] at hi
              by_cases hic : cone_w₀ i.val
              · simp [hic] at hi
              · simp only [hic, ↓reduceIte, edge, decide_eq_true_eq] at hi
                rcases hi with h_eq | h_eq
                · simp [onlyP, h_eq]
                · exact absurd hln.2 (by have hv := congrArg Fin.val h_eq; simp only [Fin.val_natAdd] at hv; simpa [hv, Nat.add_comm] using hic)
            exact ⟨heq_l ▸ hwt, evalForcedW_mono_z hAO w₀ true (outOf (edge e.1 e.2)) (onlyP e.1) hsub_out C.output hacc⟩
          have hnot_both : ¬ (ET_p.Nonempty ∧ ET_l.Nonempty) := by
            rintro ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩
            have hp1 := (hP_prop e₁ he₁).2
            have hl2 := (hL_prop e₂ he₂).1
            have hnc1 : ¬ cone_w₀ (N + e₁.2.val) := (Finset.mem_filter.mp he₁).2.2
            let z : Fin n → Bool := fun i => onlyL e₁.2 i || onlyL e₂.2 i
            have hgw : (C.wires (List.ofFn z)).getD w₀ false = true :=
              wires_mono_of_isAO2 hAO (onlyL e₂.2) z (fun i hi => by simp [z, hi]) w₀ hl2
            have hsub_out : ∀ i : Fin n, onlyL e₁.2 i = true → outOf z i = true := by
              intro i hi
              simp only [onlyL, decide_eq_true_eq] at hi
              subst hi
              have hnc1' : ¬ cone_w₀ (e₁.2.val + N) := by rw [Nat.add_comm]; exact hnc1
              simp [outOf, hnc1', z, onlyL]
            have hz_out := evalForcedW_mono_z hAO w₀ true (onlyL e₁.2) (outOf z) hsub_out C.output hp1
            have hc := heq_out z
            rw [hgw] at hc
            have hCz : circuitFun n C z = true := hc.trans hz_out
            have hsound_z : circuitFun n C z = false := by
              apply hsound z
              · rw [Fintype.card_subtype]
                have hsub : Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true) ⊆ {e₁.2, e₂.2} := by
                  intro l hl
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, z, Bool.or_eq_true,
                    onlyL, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd] at hl
                  rcases hl with h | h
                  · have hle : l = e₁.2 := Fin.ext (by omega); simp [hle]
                  · have hle : l = e₂.2 := Fin.ext (by omega); simp [hle]
                exact (Finset.card_le_card hsub).trans ((Finset.card_le_two).trans hq)
              · rintro ⟨p, l, _, hp', _⟩
                simp only [z, Bool.or_eq_true, onlyL, decide_eq_true_eq, Fin.ext_iff,
                  Fin.val_castAdd, Fin.val_natAdd] at hp'
                rcases hp' with h | h <;> omega
            rw [hsound_z] at hCz; cases hCz
          by_cases hETp_ne : ET_p.Nonempty
          · have hETl_emp : ET_l = ∅ := by
              by_contra hne
              exact hnot_both ⟨hETp_ne, Finset.nonempty_iff_ne_empty.mpr hne⟩
            have hlost_eq : ET_lost = ET_p := by
              ext e
              simp only [ET_p, Finset.mem_filter]
              refine ⟨fun he => ⟨he, ?_⟩, fun h => h.1⟩
              rcases hsplit_lost e he with h | h
              · exact h
              · exfalso
                have : e ∈ ET_l := Finset.mem_filter.mpr ⟨he, h⟩
                rw [hETl_emp] at this; simp at this
            rw [hlost_eq]
            let Pp := ET_p.image Prod.fst
            let Lp := ET_p.image Prod.snd
            have hI_all : ∀ p ∈ Pp, ∀ l ∈ Lp, I p l := by
              intro p hp l hl
              obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp hp
              obtain ⟨e₂, he₂, rfl⟩ := Finset.mem_image.mp hl
              have hp1 := (hP_prop e₁ he₁).1
              have hl2 := (hP_prop e₂ he₂).2
              have hnc2 : ¬ cone_w₀ (N + e₂.2.val) := (Finset.mem_filter.mp he₂).2.2
              have hgw : (C.wires (List.ofFn (edge e₁.1 e₂.2))).getD w₀ false = true :=
                wires_mono_of_isAO2 hAO (onlyP e₁.1) (edge e₁.1 e₂.2)
                  (fun i hi => by simp only [onlyP, decide_eq_true_eq] at hi; simp [edge, hi]) w₀ hp1
              have hsub_out : ∀ i : Fin n, onlyL e₂.2 i = true → outOf (edge e₁.1 e₂.2) i = true := by
                intro i hi
                simp only [onlyL, decide_eq_true_eq] at hi
                subst hi
                have hnc2' : ¬ cone_w₀ (e₂.2.val + N) := by rw [Nat.add_comm]; exact hnc2
                simp [outOf, hnc2', edge]
              have hz_out := evalForcedW_mono_z hAO w₀ true (onlyL e₂.2) (outOf (edge e₁.1 e₂.2)) hsub_out C.output hl2
              have hc := heq_out (edge e₁.1 e₂.2)
              rw [hgw] at hc
              have hC_t : circuitFun n C (edge e₁.1 e₂.2) = true := hc.trans hz_out
              by_contra hno
              have h0 : circuitFun n C (edge e₁.1 e₂.2) = false := by
                apply hsound (edge e₁.1 e₂.2)
                · rw [Fintype.card_subtype]
                  have hsub : Finset.univ.filter (fun l' : Fin N => edge e₁.1 e₂.2 (Fin.natAdd N l') = true) ⊆ {e₂.2} := by
                    intro l' hl'
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and, edge, decide_eq_true_eq,
                      Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl'
                    rcases hl' with h1 | h2
                    · have := e₁.1.isLt; omega
                    · exact Finset.mem_singleton.mpr (Fin.ext (by omega))
                  exact (Finset.card_le_card hsub).trans (by simp; omega)
                · rintro ⟨p', l', hi, hp', hl'⟩
                  simp only [edge, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp' hl'
                  rcases hp' with h1 | h2
                  · rcases hl' with h3 | h4
                    · have := p'.isLt; omega
                    · have hp_eq : p' = e₁.1 := Fin.ext h1
                      have hl_eq : l' = e₂.2 := Fin.ext (by omega)
                      exact hno (by rwa [← hp_eq, ← hl_eq])
                  · have := e₂.2.isLt; omega
              rw [h0] at hC_t; cases hC_t
            have hsub_prod : ET_p ⊆ Pp ×ˢ Lp := fun e he =>
              Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
            by_cases hPp : Pp.card ≤ 1
            · have hLp_le : Lp.card ≤ q + 1 := by
                rcases Nat.eq_zero_or_pos Pp.card with h0 | hpos
                · rw [Finset.card_eq_zero] at h0
                  obtain ⟨e₁, he₁⟩ := hETp_ne
                  have : e₁.1 ∈ Pp := Finset.mem_image_of_mem _ he₁
                  rw [h0] at this; simp at this
                · obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp hpos
                  have hsubL : Lp ⊆ Finset.univ.filter (fun l : Fin N => I p₀ l) := fun l hl =>
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI_all p₀ hp₀ l hl⟩
                  calc Lp.card ≤ (Finset.univ.filter (fun l : Fin N => I p₀ l)).card := Finset.card_le_card hsubL
                    _ = q + 1 := by simpa [Fintype.card_subtype] using hrow p₀
              calc ET_p.card ≤ (Pp ×ˢ Lp).card := Finset.card_le_card hsub_prod
                _ = Pp.card * Lp.card := Finset.card_product _ _
                _ ≤ 1 * (q + 1) := Nat.mul_le_mul hPp hLp_le
                _ = q + 1 := one_mul _
            · have hLp : Lp.card ≤ 1 := by
                by_contra hLp'
                push Not at hPp hLp'
                obtain ⟨p₁, hp₁, p₂, hp₂, hpp⟩ := Finset.one_lt_card.mp hPp
                obtain ⟨l₁, hl₁, l₂, hl₂, hll⟩ := Finset.one_lt_card.mp hLp'
                exact hfour p₁ p₂ l₁ l₂ hpp hll ⟨hI_all p₁ hp₁ l₁ hl₁, hI_all p₂ hp₂ l₁ hl₁,
                  hI_all p₁ hp₁ l₂ hl₂, hI_all p₂ hp₂ l₂ hl₂⟩
              have hPp_le : Pp.card ≤ q + 1 := by
                rcases Nat.eq_zero_or_pos Lp.card with h0 | hpos
                · rw [Finset.card_eq_zero] at h0
                  obtain ⟨e₁, he₁⟩ := hETp_ne
                  have : e₁.2 ∈ Lp := Finset.mem_image_of_mem _ he₁
                  rw [h0] at this; simp at this
                · obtain ⟨l₀, hl₀⟩ := Finset.card_pos.mp hpos
                  have hsubP : Pp ⊆ Finset.univ.filter (fun p : Fin N => I p l₀) := fun p hp =>
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI_all p hp l₀ hl₀⟩
                  calc Pp.card ≤ (Finset.univ.filter (fun p : Fin N => I p l₀)).card := Finset.card_le_card hsubP
                    _ = q + 1 := by simpa [Fintype.card_subtype] using hcol l₀
              calc ET_p.card ≤ (Pp ×ˢ Lp).card := Finset.card_le_card hsub_prod
                _ = Pp.card * Lp.card := Finset.card_product _ _
                _ ≤ (q + 1) * 1 := Nat.mul_le_mul hPp_le hLp
                _ = q + 1 := mul_one _
          · rw [Finset.not_nonempty_iff_eq_empty] at hETp_ne
            have hlost_eq : ET_lost = ET_l := by
              ext e
              simp only [ET_l, Finset.mem_filter]
              refine ⟨fun he => ⟨he, ?_⟩, fun h => h.1⟩
              rcases hsplit_lost e he with h | h
              · exfalso
                have : e ∈ ET_p := Finset.mem_filter.mpr ⟨he, h⟩
                rw [hETp_ne] at this; simp at this
              · exact h
            rw [hlost_eq]
            by_cases hETl_ne : ET_l.Nonempty
            · let Pl := ET_l.image Prod.fst
              let Ll := ET_l.image Prod.snd
              have hI_all : ∀ p ∈ Pl, ∀ l ∈ Ll, I p l := by
                intro p hp l hl
                obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp hp
                obtain ⟨e₂, he₂, rfl⟩ := Finset.mem_image.mp hl
                have hp1 := (hL_prop e₁ he₁).2
                have hl2 := (hL_prop e₂ he₂).1
                have hnc1 : ¬ cone_w₀ e₁.1.val := (Finset.mem_filter.mp he₁).2.1
                have hgw : (C.wires (List.ofFn (edge e₁.1 e₂.2))).getD w₀ false = true :=
                  wires_mono_of_isAO2 hAO (onlyL e₂.2) (edge e₁.1 e₂.2)
                    (fun i hi => by simp only [onlyL, decide_eq_true_eq] at hi; simp [edge, hi]) w₀ hl2
                have hsub_out : ∀ i : Fin n, onlyP e₁.1 i = true → outOf (edge e₁.1 e₂.2) i = true := by
                  intro i hi
                  simp only [onlyP, decide_eq_true_eq] at hi
                  subst hi
                  simp [outOf, hnc1, edge]
                have hz_out := evalForcedW_mono_z hAO w₀ true (onlyP e₁.1) (outOf (edge e₁.1 e₂.2)) hsub_out C.output hp1
                have hc := heq_out (edge e₁.1 e₂.2)
                rw [hgw] at hc
                have hC_t : circuitFun n C (edge e₁.1 e₂.2) = true := hc.trans hz_out
                by_contra hno
                have h0 : circuitFun n C (edge e₁.1 e₂.2) = false := by
                  apply hsound (edge e₁.1 e₂.2)
                  · rw [Fintype.card_subtype]
                    have hsub : Finset.univ.filter (fun l' : Fin N => edge e₁.1 e₂.2 (Fin.natAdd N l') = true) ⊆ {e₂.2} := by
                      intro l' hl'
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and, edge, decide_eq_true_eq,
                        Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl'
                      rcases hl' with h1 | h2
                      · have := e₁.1.isLt; omega
                      · exact Finset.mem_singleton.mpr (Fin.ext (by omega))
                    exact (Finset.card_le_card hsub).trans (by simp; omega)
                  · rintro ⟨p', l', hi, hp', hl'⟩
                    simp only [edge, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp' hl'
                    rcases hp' with h1 | h2
                    · rcases hl' with h3 | h4
                      · have := p'.isLt; omega
                      · have hp_eq : p' = e₁.1 := Fin.ext h1
                        have hl_eq : l' = e₂.2 := Fin.ext (by omega)
                        exact hno (by rwa [← hp_eq, ← hl_eq])
                    · have := e₂.2.isLt; omega
                rw [h0] at hC_t; cases hC_t
              have hsub_prod : ET_l ⊆ Pl ×ˢ Ll := fun e he =>
                Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
              by_cases hPl : Pl.card ≤ 1
              · have hLl_le : Ll.card ≤ q + 1 := by
                  obtain ⟨p₀, hp₀⟩ : ∃ p₀, p₀ ∈ Pl := ⟨(Classical.choose hETl_ne).1,
                    Finset.mem_image_of_mem _ (Classical.choose_spec hETl_ne)⟩
                  have hsubL : Ll ⊆ Finset.univ.filter (fun l : Fin N => I p₀ l) := fun l hl =>
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI_all p₀ hp₀ l hl⟩
                  calc Ll.card ≤ (Finset.univ.filter (fun l : Fin N => I p₀ l)).card := Finset.card_le_card hsubL
                    _ = q + 1 := by simpa [Fintype.card_subtype] using hrow p₀
                calc ET_l.card ≤ (Pl ×ˢ Ll).card := Finset.card_le_card hsub_prod
                  _ = Pl.card * Ll.card := Finset.card_product _ _
                  _ ≤ 1 * (q + 1) := Nat.mul_le_mul hPl hLl_le
                  _ = q + 1 := one_mul _
              · have hLl : Ll.card ≤ 1 := by
                  by_contra hLl'
                  push Not at hPl hLl'
                  obtain ⟨p₁, hp₁, p₂, hp₂, hpp⟩ := Finset.one_lt_card.mp hPl
                  obtain ⟨l₁, hl₁, l₂, hl₂, hll⟩ := Finset.one_lt_card.mp hLl'
                  exact hfour p₁ p₂ l₁ l₂ hpp hll ⟨hI_all p₁ hp₁ l₁ hl₁, hI_all p₂ hp₂ l₁ hl₁,
                    hI_all p₁ hp₁ l₂ hl₂, hI_all p₂ hp₂ l₂ hl₂⟩
                have hPl_le : Pl.card ≤ q + 1 := by
                  obtain ⟨l₀, hl₀⟩ : ∃ l₀, l₀ ∈ Ll := ⟨(Classical.choose hETl_ne).2,
                    Finset.mem_image_of_mem _ (Classical.choose_spec hETl_ne)⟩
                  have hsubP : Pl ⊆ Finset.univ.filter (fun p : Fin N => I p l₀) := fun p hp =>
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI_all p hp l₀ hl₀⟩
                  calc Pl.card ≤ (Finset.univ.filter (fun p : Fin N => I p l₀)).card := Finset.card_le_card hsubP
                    _ = q + 1 := by simpa [Fintype.card_subtype] using hcol l₀
                calc ET_l.card ≤ (Pl ×ˢ Ll).card := Finset.card_le_card hsub_prod
                  _ = Pl.card * Ll.card := Finset.card_product _ _
                  _ ≤ (q + 1) * 1 := Nat.mul_le_mul hPl_le hLl
                  _ = q + 1 := mul_one _
            · rw [Finset.not_nonempty_iff_eq_empty] at hETl_ne
              rw [hETl_ne]; simp



private lemma plane_c4_bound (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l'))
    (ET : Finset (Fin N × Fin N)) (hET : ∀ e ∈ ET, I e.1 e.2) :
    ET.card ^ 2 ≤ (ET.image Prod.snd).card * (ET.image Prod.fst).card * ((ET.image Prod.fst).card - 1) +
      (ET.image Prod.snd).card * ET.card := by
  classical
  let PT := ET.image Prod.fst
  let LT := ET.image Prod.snd
  let degL : Fin N → ℕ := fun l => (ET.filter fun e => e.2 = l).card
  have hsum : ∑ l ∈ LT, degL l = ET.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_filter, LT, Finset.mem_image]
      constructor
      · rintro ⟨l, _, he, _⟩; exact he
      · intro he; exact ⟨e.2, ⟨e, he, rfl⟩, he, rfl⟩
    · intro l₁ _ l₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro e h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hcs : ET.card ^ 2 ≤ LT.card * ∑ l ∈ LT, degL l ^ 2 := by
    rw [← hsum]
    have hcsZ : 2 * (∑ l ∈ LT, (degL l : ℤ)) ^ 2 ≤ 2 * (LT.card : ℤ) * ∑ l ∈ LT, (degL l : ℤ) ^ 2 := by
      have hid : 2 * (LT.card : ℤ) * (∑ l ∈ LT, (degL l : ℤ) ^ 2) - 2 * (∑ l ∈ LT, (degL l : ℤ)) ^ 2 =
          ∑ a ∈ LT, ∑ b ∈ LT, ((degL a : ℤ) - (degL b : ℤ)) ^ 2 := by
        have hsq : ∀ a b : Fin N, ((degL a : ℤ) - (degL b : ℤ)) ^ 2 =
            (degL a : ℤ) ^ 2 - 2 * (degL a : ℤ) * (degL b : ℤ) + (degL b : ℤ) ^ 2 := fun a b => by ring
        simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum, ← Finset.sum_mul]
        have h2sum : (∑ i ∈ LT, (2 : ℤ) * (degL i : ℤ)) = 2 * ∑ i ∈ LT, (degL i : ℤ) :=
          (Finset.mul_sum LT _ 2).symm
        rw [h2sum, sq]
        ring
      have hnn : 0 ≤ ∑ a ∈ LT, ∑ b ∈ LT, ((degL a : ℤ) - (degL b : ℤ)) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      linarith
    zify
    linarith
  -- Count ordered triples (p, p', l) with p ≠ p', (p, l) ∈ ET, (p', l) ∈ ET
  let T := (LT ×ˢ PT ×ˢ PT).filter fun x =>
    x.2.1 ≠ x.2.2 ∧ (x.2.1, x.1) ∈ ET ∧ (x.2.2, x.1) ∈ ET
  have hT_eq_L : T.card = ∑ l ∈ LT, degL l * (degL l - 1) := by
    let fl : Fin N → Finset (Fin N × Fin N × Fin N) := fun l => T.filter fun x => x.1 = l
    have hT_part : T = LT.biUnion fl := by
      ext x
      simp only [Finset.mem_biUnion, fl, Finset.mem_filter, T, Finset.mem_product]
      constructor
      · intro hx; exact ⟨x.1, hx.1.1, hx, rfl⟩
      · rintro ⟨l, _, hx, _⟩; exact hx
    have hfl_disj : Set.PairwiseDisjoint (↑LT) fl := by
      intro l₁ _ l₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hfl_card : ∀ l ∈ LT, (fl l).card = degL l * (degL l - 1) := by
      intro l hl
      let Pl := (ET.filter fun e => e.2 = l).image Prod.fst
      have hPl_card : Pl.card = degL l := by
        apply Finset.card_image_of_injOn
        intro e₁ h1 e₂ h2 heq
        exact Prod.ext heq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
      have hbij : fl l = ((Pl ×ˢ Pl).filter fun p => p.1 ≠ p.2).image (fun p => (l, p.1, p.2)) := by
        ext ⟨l', p₁, p₂⟩
        simp only [fl, Finset.mem_filter, T, Finset.mem_product, Finset.mem_image, Pl]
        constructor
        · rintro ⟨⟨⟨_, _, _⟩, hne, h1, h2⟩, hll⟩
          subst l'
          exact ⟨(p₁, p₂), ⟨⟨⟨(p₁, l), ⟨h1, rfl⟩, rfl⟩, ⟨(p₂, l), ⟨h2, rfl⟩, rfl⟩⟩, hne⟩, rfl⟩
        · rintro ⟨⟨a, b⟩, ⟨⟨⟨e₁, ⟨he1, he1l⟩, he1p⟩, ⟨e₂, ⟨he2, he2l⟩, he2p⟩⟩, hne⟩, heq⟩
          obtain ⟨hl_eq, hp_eq⟩ := Prod.mk.inj heq
          obtain ⟨hp1_eq, hp2_eq⟩ := Prod.mk.inj hp_eq
          subst p₁ p₂
          dsimp only at *
          have he1' : (a, l') ∈ ET := by rw [← he1p, ← hl_eq, ← he1l]; exact he1
          have he2' : (b, l') ∈ ET := by rw [← he2p, ← hl_eq, ← he2l]; exact he2
          exact ⟨⟨⟨hl_eq ▸ hl, Finset.mem_image_of_mem _ he1', Finset.mem_image_of_mem _ he2'⟩, hne, he1', he2'⟩, hl_eq.symm⟩
      rw [hbij, Finset.card_image_of_injective _ (fun _ _ h =>
        Prod.ext (Prod.mk.inj (Prod.mk.inj h).2).1 (Prod.mk.inj (Prod.mk.inj h).2).2)]
      have h_off : ((Pl ×ˢ Pl).filter fun p => p.1 ≠ p.2).card + Pl.card = Pl.card * Pl.card := by
        have hdiag : (Pl ×ˢ Pl).filter (fun p => p.1 = p.2) = Pl.image (fun p => (p, p)) := by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl⟩
          · rintro ⟨c, hc, heq⟩; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact ⟨⟨hc, hc⟩, rfl⟩
        have hpart' : ((Pl ×ˢ Pl).filter fun p => p.1 ≠ p.2) ∪ ((Pl ×ˢ Pl).filter fun p => p.1 = p.2) = Pl ×ˢ Pl := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]; tauto
        have hdisj' : Disjoint ((Pl ×ˢ Pl).filter fun p => p.1 ≠ p.2) ((Pl ×ˢ Pl).filter fun p => p.1 = p.2) := by
          rw [Finset.disjoint_left]; intro p h1 h2; exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        have hcu := Finset.card_union_of_disjoint hdisj'
        rw [hpart', Finset.card_product] at hcu
        have hdcard : ((Pl ×ˢ Pl).filter fun p => p.1 = p.2).card = Pl.card := by
          rw [hdiag]; exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        omega
      rw [hPl_card] at h_off
      have : degL l * (degL l - 1) + degL l = degL l * degL l := by
        cases h : degL l with
        | zero => simp
        | succ d => simp; ring
      omega
    rw [hT_part, Finset.card_biUnion hfl_disj]
    exact Finset.sum_congr rfl hfl_card
  have hT_le_P : T.card ≤ PT.card * (PT.card - 1) := by
    have himg : T.image (fun x => (x.2.1, x.2.2)) ⊆ (PT ×ˢ PT).filter fun p => p.1 ≠ p.2 := by
      intro p hp
      obtain ⟨⟨l, p₁, p₂⟩, hx, heq⟩ := Finset.mem_image.mp hp
      have hxm := Finset.mem_filter.mp hx
      have hxp := Finset.mem_product.mp hxm.1
      have hp' := Finset.mem_product.mp hxp.2
      change (p₁, p₂) = p at heq
      rw [← heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp'.1, hp'.2⟩, hxm.2.1⟩
    have hinj : Set.InjOn (fun x : Fin N × Fin N × Fin N => (x.2.1, x.2.2)) T := by
      intro ⟨l₁, p₁, p₂⟩ hx₁ ⟨l₂, q₁, q₂⟩ hx₂ heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      have h1 := (Finset.mem_filter.mp hx₁).2
      have h2 := (Finset.mem_filter.mp hx₂).2
      by_cases hl : l₁ = l₂
      · rw [hl]
      · exfalso
        exact hfour p₁ p₂ l₁ l₂ h1.1 hl ⟨hET _ h1.2.1, hET _ h1.2.2, hET _ h2.2.1, hET _ h2.2.2⟩
    have h_off : ((PT ×ˢ PT).filter fun p => p.1 ≠ p.2).card + PT.card = PT.card * PT.card := by
      have hdiag : (PT ×ˢ PT).filter (fun p => p.1 = p.2) = PT.image (fun p => (p, p)) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl⟩
        · rintro ⟨c, hc, heq⟩; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact ⟨⟨hc, hc⟩, rfl⟩
      have hpart' : ((PT ×ˢ PT).filter fun p => p.1 ≠ p.2) ∪ ((PT ×ˢ PT).filter fun p => p.1 = p.2) = PT ×ˢ PT := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]; tauto
      have hdisj' : Disjoint ((PT ×ˢ PT).filter fun p => p.1 ≠ p.2) ((PT ×ˢ PT).filter fun p => p.1 = p.2) := by
        rw [Finset.disjoint_left]; intro p h1 h2; exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hcu := Finset.card_union_of_disjoint hdisj'
      rw [hpart', Finset.card_product] at hcu
      have hdcard : ((PT ×ˢ PT).filter fun p => p.1 = p.2).card = PT.card := by
        rw [hdiag]; exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
      omega
    calc T.card = (T.image (fun x => (x.2.1, x.2.2))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((PT ×ˢ PT).filter fun p => p.1 ≠ p.2).card := Finset.card_le_card himg
      _ = PT.card * (PT.card - 1) := by
        cases h : PT.card with
        | zero => rw [h] at h_off; simp only [Nat.add_zero, Nat.zero_mul] at h_off ⊢; exact h_off
        | succ d => simp only [Nat.succ_sub_one]; rw [h] at h_off; nlinarith
  have hsq_sum : ∑ l ∈ LT, degL l ^ 2 = ∑ l ∈ LT, (degL l * (degL l - 1) + degL l) := by
    apply Finset.sum_congr rfl
    intro l _
    cases h : degL l with
    | zero => simp
    | succ d => simp; ring
  rw [hsq_sum, Finset.sum_add_distrib, ← hT_eq_L, hsum] at hcs
  calc ET.card ^ 2 ≤ LT.card * (T.card + ET.card) := hcs
    _ = LT.card * T.card + LT.card * ET.card := by ring
    _ ≤ LT.card * (PT.card * (PT.card - 1)) + LT.card * ET.card :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hT_le_P) _
    _ = LT.card * PT.card * (PT.card - 1) + LT.card * ET.card := by ring

private lemma plane_arith (q s P L B m : ℕ)
    (hq2 : 2 ≤ q) (hq130 : q ≤ 130) (hs1 : 1 ≤ s)
    (hPLB : P + L + B ≤ s + 1)
    (hmB : m ≤ P + L + (q + 1) * B)
    (hmP : m ≤ P * (q + 1))
    (hmL : m ≤ L * (q + 1))
    (hmPL : m ≤ P * L)
    (hc4 : m ^ 2 ≤ L * P * (P - 1) + L * m) :
    m ≤ 44 * s := by
  by_cases hs173 : s ≤ 173
  · have h4PL : 4 * P * L ≤ (P + L) ^ 2 := by nlinarith [sq_nonneg ((P : ℤ) - L)]
    have hPL_le : P + L ≤ s + 1 := by omega
    have hs_bd : (s + 1) ^ 2 ≤ 176 * s := by nlinarith
    have h4m : 4 * m ≤ 4 * P * L := by nlinarith
    nlinarith
  · by_cases hs174 : s = 174
    · subst hs174
      have hPL_le : P + L ≤ 175 := by omega
      by_cases hP87 : P ≤ 87
      · nlinarith
      · have hL87 : L ≤ 87 := by omega
        nlinarith
    · by_cases hs399 : s ≤ 399
      · have hs175 : 175 ≤ s := by omega
        have hPL_le : P + L ≤ s + 1 := by omega
        have hamgm : 27 * L * P ^ 2 ≤ 4 * (P + L) ^ 3 := by
          have h1 : (0 : ℤ) ≤ ((P : ℤ) - 2 * L) ^ 2 * (4 * P + L) := by positivity
          have h2 : (4 * ((P : ℤ) + L) ^ 3 - 27 * L * P ^ 2) = (P - 2 * L) ^ 2 * (4 * P + L) := by ring
          zify
          linarith
        have hP3 : L * P * (P - 1) ≤ L * P ^ 2 := by
          calc L * P * (P - 1) ≤ L * P * P := Nat.mul_le_mul_left _ (Nat.sub_le P 1)
            _ = L * P ^ 2 := by ring
        have h27m : 27 * m ^ 2 ≤ 4 * (s + 1) ^ 3 + 27 * (s + 1) * m := by
          have hL_le : L ≤ s + 1 := by omega
          have hcub : 4 * (P + L) ^ 3 ≤ 4 * (s + 1) ^ 3 := by
            exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hPL_le 3)
          nlinarith
        by_contra hbig
        push Not at hbig
        have hm_ge : 44 * s + 1 ≤ m := hbig
        have h1 : 27 * m * (m - (s + 1)) ≤ 4 * (s + 1) ^ 3 := by
          have : 27 * (s + 1) * m ≤ 27 * m ^ 2 := by nlinarith
          zify [show s + 1 ≤ m by omega]
          zify at h27m
          linarith
        have hs_cub : (s + 1) ^ 3 ≤ 400 ^ 2 * (s + 1) := by
          have : (s + 1) ^ 2 ≤ 400 ^ 2 := Nat.pow_le_pow_left (by omega) 2
          nlinarith
        have hcontra : 4 * (s + 1) ^ 3 < 27 * m * (m - (s + 1)) := by
          have hms : 43 * s ≤ m - (s + 1) := by omega
          have hm_lo : 44 * 175 ≤ m := by omega
          nlinarith
        omega
      · have hs400 : 400 ≤ s := by omega
        have hkey : (3 * q + 1) * m ≤ (q + 1) ^ 2 * (s + 1) := by
          have h1 : q * m ≤ q * ((q + 1) * P) := Nat.mul_le_mul_left q (by rw [Nat.mul_comm]; exact hmP)
          have h2 : q * m ≤ q * ((q + 1) * L) := Nat.mul_le_mul_left q (by rw [Nat.mul_comm]; exact hmL)
          have h3 : (q + 1) * m ≤ (q + 1) * (P + L + (q + 1) * B) := Nat.mul_le_mul_left (q + 1) hmB
          have hid : q * ((q + 1) * P) + q * ((q + 1) * L) + (q + 1) * (P + L + (q + 1) * B) =
              (q + 1) ^ 2 * (P + L + B) := by ring
          have hlhs : (3 * q + 1) * m = q * m + q * m + (q + 1) * m := by ring
          calc (3 * q + 1) * m = q * m + q * m + (q + 1) * m := hlhs
            _ ≤ q * ((q + 1) * P) + q * ((q + 1) * L) + (q + 1) * (P + L + (q + 1) * B) := by omega
            _ = (q + 1) ^ 2 * (P + L + B) := hid
            _ ≤ (q + 1) ^ 2 * (s + 1) := Nat.mul_le_mul_left _ hPLB
        have hq_diff : (q + 1) ^ 2 * (s + 1) ≤ 44 * (3 * q + 1) * s := by
          zify
          have h1 : (0 : ℤ) ≤ q * (130 - q) * s := by
            have : (0 : ℤ) ≤ q := by omega
            have : (0 : ℤ) ≤ 130 - q := by omega
            have : (0 : ℤ) ≤ s := by omega
            positivity
          have h2 : (43 : ℤ) * s ≥ (q + 1) ^ 2 := by nlinarith
          have hid : 44 * (3 * (q : ℤ) + 1) * s - (q + 1) ^ 2 * (s + 1) =
              q * (130 - q) * s + (43 * s - (q + 1) ^ 2) := by ring
          linarith
        have hfinal : (3 * q + 1) * m ≤ (3 * q + 1) * (44 * s) := by
          calc (3 * q + 1) * m ≤ (q + 1) ^ 2 * (s + 1) := hkey
            _ ≤ 44 * (3 * q + 1) * s := hq_diff
            _ = (3 * q + 1) * (44 * s) := by ring
        exact Nat.le_of_mul_le_mul_left hfinal (by omega)


end PEqualNP.Outside.L_meta_3289

theorem PEqualNP.Outside.L_meta_3289 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x13.1 ∨ x14 = Fin.natAdd x2 x13.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I _ C hq2 hq130 hN hcol huniq hmono hsound
  let ET : Finset (Fin N × Fin N) := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun i => Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = Bool.true
  rw [Fintype.card_subtype]
  change ET.card ≤ 44 * C.size
  by_cases hET_emp : ET = ∅
  · rw [hET_emp]; simp
  have hET_ne : ET.Nonempty := Finset.nonempty_iff_ne_empty.mpr hET_emp
  have hET_mem : ∀ e ∈ ET, I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  obtain ⟨C1, hAO, hsz, hC1_le, hC1_ET⟩ :=
    PEqualNP.Outside.L_meta_3289.reduce_to_AO2 q N I C hmono hsound ET hET_mem hET_ne
  have hC1_sound : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C1 z = false := by
    intro z hz hno
    cases hv : PEqualNP.MetaComplexity.circuitFun (N + N) C1 z
    · rfl
    · have hc := hC1_le z hv
      rw [hsound z hz hno] at hc
      cases hc
  have hC1_ET' : ∀ e ∈ ET, I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C1
      (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true :=
    fun e he => ⟨(hET_mem e he).1, hC1_ET e he⟩
  have hfour := PEqualNP.Outside.L_meta_3289.plane_four_free N I huniq
  have hrow : ∀ p : Fin N, Fintype.card { l : Fin N // I p l } = q + 1 := by
    intro p
    rw [Fintype.card_subtype]
    exact PEqualNP.Outside.L_meta_3289.plane_pt_deg q N I (by omega) hN hcol huniq p
  let n := N + N
  let reach : ℕ → Prop := fun a =>
    Relation.ReflTransGen (PEqualNP.Outside.L_meta_3289.stepR C1 n) a C1.output
  let R : Finset (Fin C1.size) := Finset.univ.filter fun j => reach (n + j.val)
  let Sread : Finset ℕ := R.biUnion fun j => (C1.gates[j.val]'j.isLt).inputs.toFinset
  let deg : ℕ → ℕ := fun w =>
    ((R ×ˢ (Finset.univ : Finset (Fin 2))).filter fun jb =>
      (C1.gates[jb.1.val]'jb.1.isLt).inputs.getD jb.2.val 0 = w).card
  let B : ℕ := ∑ w ∈ Sread, (deg w - 1)
  obtain ⟨hmB, hPLB⟩ := PEqualNP.Outside.L_meta_3289.branching_bound q N I hq2 hcol hrow hfour
    B C1 hAO hC1_sound ET hC1_ET' rfl
  let PT := ET.image Prod.fst
  let LT := ET.image Prod.snd
  have hmPL : ET.card ≤ PT.card * LT.card := by
    have hsub : ET ⊆ PT ×ˢ LT := fun e he =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
    simpa [Finset.card_product] using Finset.card_le_card hsub
  have hmL : ET.card ≤ LT.card * (q + 1) := by
    have hsubL : ET ⊆ LT.biUnion (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
      intro e he
      refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_image_of_mem _ he, ?_⟩
      exact Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hET_mem e he).1⟩, rfl⟩
    calc ET.card ≤ ∑ l ∈ LT, ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card :=
          (Finset.card_le_card hsubL).trans Finset.card_biUnion_le
      _ ≤ ∑ l ∈ LT, (Finset.univ.filter (fun p : Fin N => I p l)).card :=
          Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = ∑ _l ∈ LT, (q + 1) := Finset.sum_congr rfl (fun l _ => by simpa [Fintype.card_subtype] using hcol l)
      _ = LT.card * (q + 1) := by simp
  have hmP : ET.card ≤ PT.card * (q + 1) := by
    have hsubP : ET ⊆ PT.biUnion (fun p => (Finset.univ.filter (fun l : Fin N => I p l)).image (fun l => (p, l))) := by
      intro e he
      refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_image_of_mem _ he, ?_⟩
      exact Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hET_mem e he).1⟩, rfl⟩
    calc ET.card ≤ ∑ p ∈ PT, ((Finset.univ.filter (fun l : Fin N => I p l)).image (fun l => (p, l))).card :=
          (Finset.card_le_card hsubP).trans Finset.card_biUnion_le
      _ ≤ ∑ p ∈ PT, (Finset.univ.filter (fun l : Fin N => I p l)).card :=
          Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = ∑ _p ∈ PT, (q + 1) := Finset.sum_congr rfl (fun p _ => by simpa [Fintype.card_subtype] using hrow p)
      _ = PT.card * (q + 1) := by simp
  have hc4 := PEqualNP.Outside.L_meta_3289.plane_c4_bound N I hfour ET (fun e he => (hET_mem e he).1)
  have hC1_pos : 1 ≤ C1.size := by
    obtain ⟨e₀, he₀⟩ := hET_ne
    have hm := (hC1_ET' e₀ he₀).2
    by_contra h0
    push Not at h0
    have hsz0 : C1.gates.length = 0 := by change C1.size = 0; omega
    have hnil : C1.gates = [] := List.eq_nil_of_length_eq_zero hsz0
    by_cases hlt : C1.output < N + N
    · have hout : ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C1 z = z ⟨C1.output, hlt⟩ := by
        intro z
        change (C1.wires (List.ofFn z)).getD C1.output false = _
        rw [PEqualNP.Outside.L_meta_3289.wires_eq_runW, hnil, PEqualNP.Outside.L_meta_3289.runW_nil]
        simp [List.getD_eq_getElem?_getD, hlt]
      by_cases hp : C1.output < N
      · have h1 := hout (fun k => decide (k = Fin.castAdd N ⟨C1.output, hp⟩))
        have h0' := hC1_sound (fun k => decide (k = Fin.castAdd N ⟨C1.output, hp⟩))
          (by rw [Fintype.card_subtype]
              have hemp : Finset.univ.filter (fun l : Fin N => decide (Fin.natAdd N l = Fin.castAdd N ⟨C1.output, hp⟩) = true) = ∅ := by
                ext l
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
                  decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
                omega
              rw [hemp]; simp)
          (by rintro ⟨_, l, _, _, hl⟩; simp [Fin.ext_iff] at hl; omega)
        rw [h0'] at h1; simp at h1
      · have h1 := hout (fun k => decide (k = Fin.natAdd N ⟨C1.output - N, by omega⟩))
        have h0' := hC1_sound (fun k => decide (k = Fin.natAdd N ⟨C1.output - N, by omega⟩))
          (by rw [Fintype.card_subtype]
              have hsub : Finset.univ.filter (fun l : Fin N => decide (Fin.natAdd N l = Fin.natAdd N ⟨C1.output - N, by omega⟩) = true) ⊆ {⟨C1.output - N, by omega⟩} := by
                intro l hl; simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd] at hl
                exact Finset.mem_singleton.mpr (Fin.ext (by dsimp only; omega))
              exact (Finset.card_le_card hsub).trans (by simp; omega))
          (by rintro ⟨p, _, _, hp, _⟩; simp [Fin.ext_iff] at hp; omega)
        rw [h0'] at h1
        have hidx : (⟨C1.output, hlt⟩ : Fin (N + N)) = Fin.natAdd N ⟨C1.output - N, by omega⟩ :=
          Fin.ext (by simp only [Fin.val_natAdd]; omega)
        simp only [hidx, decide_true] at h1
        cases h1
    · have hge : (C1.wires (List.ofFn (fun i : Fin (N + N) => decide (i = Fin.castAdd N e₀.1 ∨ i = Fin.natAdd N e₀.2)))).length ≤ C1.output := by
        rw [PEqualNP.Outside.L_meta_3289.wires_eq_runW, PEqualNP.Outside.L_meta_3289.runW_len, List.length_ofFn]
        change N + N + C1.gates.length ≤ C1.output; omega
      have hf : PEqualNP.MetaComplexity.circuitFun (N + N) C1
          (fun i => decide (i = Fin.castAdd N e₀.1 ∨ i = Fin.natAdd N e₀.2)) = false := by
        change (C1.wires _).getD C1.output false = false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
      rw [hf] at hm; cases hm
  have hle_C1 := PEqualNP.Outside.L_meta_3289.plane_arith q C1.size PT.card LT.card B ET.card
    hq2 hq130 hC1_pos hPLB hmB hmP hmL hmPL hc4
  exact hle_C1.trans (Nat.mul_le_mul_left 44 hsz)
