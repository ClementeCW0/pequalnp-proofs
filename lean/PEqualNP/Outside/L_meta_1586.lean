import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1586

open PEqualNP.CircuitLowerBounds

def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  Circuit.wires ⟨gs, 0⟩ x

def gateStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma evalWires_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    evalWires (g :: gs) x = evalWires gs (x ++ [gateStep x g]) := rfl

lemma evalWires_append (A B : List Gate) (x : List Bool) :
    evalWires (A ++ B) x = evalWires B (evalWires A x) := by
  simp only [evalWires, Circuit.wires, List.foldl_append]

lemma evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalWires, Circuit.wires]
  | cons g gs ih =>
    rw [evalWires_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma evalWires_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (evalWires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [evalWires_cons, ih _ (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma evalWires_getD_ge (gs : List Gate) (x : List Bool) (i : ℕ)
    (hi : x.length + gs.length ≤ i) :
    (evalWires gs x).getD i false = false := by
  rw [List.getD_eq_getElem?_getD]
  have hlen : (evalWires gs x).length ≤ i := by rw [evalWires_length]; exact hi
  rw [List.getElem?_eq_none hlen]
  rfl

lemma evalWires_take_getD (gs : List Gate) (x : List Bool) (k i : ℕ)
    (hi : i < x.length + k) :
    (evalWires (gs.take k) x).getD i false = (evalWires gs x).getD i false := by
  by_cases hk : k ≤ gs.length
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, evalWires_append]
    have hlen : i < (evalWires (gs.take k) x).length := by
      rw [evalWires_length, List.length_take, Nat.min_eq_left hk]
      exact hi
    exact (evalWires_getD_lt _ _ _ hlen).symm
  · rw [List.take_of_length_le (Nat.le_of_not_ge hk)]

lemma eval_input {N : ℕ} (gs : List Gate) (x : Fin N → Bool) (p : Fin N) :
    Circuit.eval ⟨gs, p.val⟩ (List.ofFn x) = x p := by
  change (evalWires gs (List.ofFn x)).getD p.val false = x p
  rw [evalWires_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma eval_ge {N : ℕ} (gs : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : N + gs.length ≤ w) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = false := by
  change (evalWires gs (List.ofFn x)).getD w false = false
  exact evalWires_getD_ge gs (List.ofFn x) w (by simp; exact hw)

lemma eval_gate {N : ℕ} (gs : List Gate) (x : Fin N → Bool) (i : Fin gs.length)
    (hvalid : ∀ a ∈ (gs.get i).inputs, a < N + (i : ℕ)) :
    Circuit.eval ⟨gs, N + (i : ℕ)⟩ (List.ofFn x) =
      (gs.get i).op.eval ((gs.get i).inputs.map fun a => Circuit.eval ⟨gs, a⟩ (List.ofFn x)) := by
  change (evalWires gs (List.ofFn x)).getD (N + (i : ℕ)) false = _
  have hi : (i : ℕ) < gs.length := i.isLt
  let k : ℕ := i.val
  have hk : k < gs.length := hi
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := List.take_append_drop k gs
    have h2 : gs.drop k = gs[k] :: gs.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [← h2, h1]
  have hlenx : (List.ofFn x).length = N := List.length_ofFn
  have htake_len : (evalWires (gs.take k) (List.ofFn x)).length = N + k := by
    rw [evalWires_length, hlenx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have h1 : (evalWires gs (List.ofFn x)).getD (N + k) false =
      gateStep (evalWires (gs.take k) (List.ofFn x)) (gs[k]'hk) := by
    have h0 : (evalWires (gs.take k ++ gs[k] :: gs.drop (k + 1)) (List.ofFn x)).getD (N + k) false =
        gateStep (evalWires (gs.take k) (List.ofFn x)) (gs[k]'hk) := by
      rw [evalWires_append, evalWires_cons]
      have hlt : N + k < (evalWires (gs.take k) (List.ofFn x) ++
          [gateStep (evalWires (gs.take k) (List.ofFn x)) gs[k]]).length := by
        rw [List.length_append, List.length_singleton, htake_len]; omega
      rw [evalWires_getD_lt _ _ _ hlt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), htake_len, Nat.sub_self]
      rfl
    simpa only [← hsplit] using h0
  change (evalWires gs (List.ofFn x)).getD (N + k) false = _
  rw [h1, gateStep]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact evalWires_take_getD gs (List.ofFn x) k a (by rw [hlenx]; exact hvalid a ha)

def InOrTop (N : ℕ) (gates : List Gate) (u Y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S →
    (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) →
    Y ∈ S

lemma inOrTop_step {N : ℕ} {gates : List Gate} {u : ℕ} {i : Fin gates.length} {a : ℕ}
    (hu : InOrTop N gates u (N + (i : ℕ)))
    (hor : (gates.get i).op = GateOp.or)
    (ha : a ∈ (gates.get i).inputs) :
    InOrTop N gates u a := by
  intro S hS hcl
  exact hcl i (hu S hS hcl) hor a ha

end PEqualNP.Outside.L_meta_1586

theorem PEqualNP.Outside.L_meta_1586 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hao hwf hu0
  let x0 : Fin N → Bool := fun v => decide (v ∉ L i0)
  have hpart1 : ∀ Y : ℕ, PEqualNP.Outside.L_meta_1586.InOrTop N gates u Y →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn x0) = false := by
    intro Y hY
    refine hY { w : ℕ | PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x0) = false } hu0 ?_
    intro i hi hor a ha
    have hev := PEqualNP.Outside.L_meta_1586.eval_gate gates x0 i (hwf i).2
    rw [hi, hor] at hev
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval] at hev
    have hall : ∀ b ∈ (gates.get i).inputs.map (fun w => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x0)), b = false := by
      intro b hb
      cases hbval : b
      · rfl
      · exfalso
        have hany : ((gates.get i).inputs.map (fun w => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x0))).any id = true :=
          List.any_eq_true.mpr ⟨b, hb, hbval⟩
        rw [hany] at hev
        exact Bool.false_ne_true hev
    exact hall _ (List.mem_map_of_mem ha)
  have hpart2 : ∀ p : Fin N, PEqualNP.Outside.L_meta_1586.InOrTop N gates u (p : ℕ) → p ∈ L i0 := by
    intro p hp
    have hval := hpart1 p.val hp
    rw [PEqualNP.Outside.L_meta_1586.eval_input] at hval
    simp only [x0, decide_eq_false_iff_not, not_not] at hval
    exact hval
  refine ⟨hpart1, hpart2, ?_, ?_⟩
  · intro r _ hru
    let xr : Fin N → Bool := fun v => decide (v ∉ L i0 ∨ v = r)
    have hgen : ∀ Y : ℕ, PEqualNP.Outside.L_meta_1586.InOrTop N gates u Y →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn xr) = true →
        PEqualNP.Outside.L_meta_1586.InOrTop N gates u (r : ℕ) ∨
        ∃ a : ℕ, PEqualNP.Outside.L_meta_1586.InOrTop N gates u a ∧
          (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn xr) = true := by
      intro Y
      induction Y using Nat.strong_induction_on with
      | ind Y ih =>
        intro hY hYtrue
        by_cases hYN : Y < N
        · let p : Fin N := ⟨Y, hYN⟩
          have hpL : p ∈ L i0 := hpart2 p hY
          have hev := PEqualNP.Outside.L_meta_1586.eval_input gates xr p
          rw [hev] at hYtrue
          simp only [xr, decide_eq_true_iff] at hYtrue
          rcases hYtrue with hpnot | hpr
          · exact (hpnot hpL).elim
          · left
            have hval : (r : ℕ) = Y := by rw [← hpr]
            rw [hval]
            exact hY
        · by_cases hYlt : Y - N < gates.length
          · let i : Fin gates.length := ⟨Y - N, hYlt⟩
            have hYeq : Y = N + (i : ℕ) := by dsimp [i]; omega
            rcases (hao (gates.get i) (List.get_mem _ _)).1 with hand | hor
            · right
              exact ⟨Y, hY, ⟨i, hYeq, hand⟩, hYtrue⟩
            · have hev := PEqualNP.Outside.L_meta_1586.eval_gate gates xr i (hwf i).2
              rw [← hYeq, hYtrue, hor] at hev
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval] at hev
              have hany := List.any_eq_true.mp hev.symm
              rcases hany with ⟨_, hmem, htrue⟩
              rcases List.mem_map.mp hmem with ⟨c, hc, rfl⟩
              have hc_in : PEqualNP.Outside.L_meta_1586.InOrTop N gates u c :=
                PEqualNP.Outside.L_meta_1586.inOrTop_step (hYeq ▸ hY) hor hc
              have hc_lt : c < Y := by rw [hYeq]; exact (hwf i).2 c hc
              exact ih c hc_lt hc_in htrue
          · have hge : N + gates.length ≤ Y := by omega
            have hfalse := PEqualNP.Outside.L_meta_1586.eval_ge gates xr Y hge
            rw [hfalse] at hYtrue
            exact (Bool.false_ne_true hYtrue).elim
    exact hgen u (fun _ h _ => h) hru
  · intro a c hand _ hc _ r _ htrue
    let xr : Fin N → Bool := fun v => decide (v ∉ L i0 ∨ v = r)
    have hev := PEqualNP.Outside.L_meta_1586.eval_gate gates xr a (hwf a).2
    rw [htrue, hand] at hev
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval] at hev
    have hall := List.all_eq_true.mp hev.symm
    exact hall _ (List.mem_map_of_mem hc)
