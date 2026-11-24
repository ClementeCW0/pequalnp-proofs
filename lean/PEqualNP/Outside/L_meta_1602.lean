import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1602

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

lemma evalWires_getD_gate {m : ℕ} (gs : List Gate) (x : Fin m → Bool) (k : ℕ) (hk : k < gs.length) :
    (evalWires gs (List.ofFn x)).getD (m + k) false =
      gateStep (evalWires (gs.take k) (List.ofFn x)) (gs[k]'hk) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := List.take_append_drop k gs
    have h2 : gs.drop k = gs[k] :: gs.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [← h2, h1]
  have hlenx : (List.ofFn x).length = m := List.length_ofFn
  have htake_len : (evalWires (gs.take k) (List.ofFn x)).length = m + k := by
    rw [evalWires_length, hlenx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have h0 : (evalWires (gs.take k ++ gs[k] :: gs.drop (k + 1)) (List.ofFn x)).getD (m + k) false =
      gateStep (evalWires (gs.take k) (List.ofFn x)) (gs[k]'hk) := by
    rw [evalWires_append, evalWires_cons]
    have hlt : m + k < (evalWires (gs.take k) (List.ofFn x) ++
        [gateStep (evalWires (gs.take k) (List.ofFn x)) gs[k]]).length := by
      rw [List.length_append, List.length_singleton, htake_len]; omega
    rw [evalWires_getD_lt _ _ _ hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), htake_len, Nat.sub_self]
    rfl
  simpa only [← hsplit] using h0

lemma gateStep_mono {w1 w2 : List Bool} {g : Gate}
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    gateStep w1 g = true → gateStep w2 g = true := by
  rcases hop with h | h <;> simp only [gateStep, h, GateOp.eval, List.all_eq_true,
    List.any_eq_true, List.mem_map, id_eq]
  · intro h1 b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h1 _ ⟨i, hi, rfl⟩)
  · rintro ⟨_, ⟨i, hi, rfl⟩, htrue⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hle i htrue⟩

lemma evalWires_mono {gs : List Gate}
    (hao : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {x1 x2 : List Bool} (hlen : x1.length = x2.length)
    (hx : ∀ i, x1.getD i false = true → x2.getD i false = true) :
    ∀ i, (evalWires gs x1).getD i false = true → (evalWires gs x2).getD i false = true := by
  induction gs generalizing x1 x2 with
  | nil => exact hx
  | cons g gs ih =>
    rw [evalWires_cons, evalWires_cons]
    have hao_g : g.op = GateOp.and ∨ g.op = GateOp.or := (hao g (by simp)).1
    have hao_gs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 :=
      fun h hh => hao h (by simp [hh])
    apply ih hao_gs (by simp [hlen])
    intro i hi
    by_cases hlt : i < x1.length
    · have h1 : (x1 ++ [gateStep x1 g]).getD i false = x1.getD i false := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      have h2 : (x2 ++ [gateStep x2 g]).getD i false = x2.getD i false := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen ▸ hlt)]
      rw [h1] at hi; rw [h2]
      exact hx i hi
    · by_cases heq : i = x1.length
      · subst heq
        have h1 : (x1 ++ [gateStep x1 g]).getD x1.length false = gateStep x1 g := by
          simp [List.getD_eq_getElem?_getD]
        have h2 : (x2 ++ [gateStep x2 g]).getD x1.length false = gateStep x2 g := by
          simp [List.getD_eq_getElem?_getD, hlen]
        rw [h1] at hi; rw [h2]
        exact gateStep_mono hao_g hx hi
      · have hgt : (x1 ++ [gateStep x1 g]).length ≤ i := by simp; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgt] at hi
        exact (Bool.false_ne_true hi).elim

lemma wires_mono {m : ℕ} {gs : List Gate}
    (hao : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {x1 x2 : Fin m → Bool} (hx : ∀ v : Fin m, x1 v = true → x2 v = true) (i : ℕ) :
    (evalWires gs (List.ofFn x1)).getD i false = true →
      (evalWires gs (List.ofFn x2)).getD i false = true := by
  apply evalWires_mono hao (by simp)
  intro j hj
  by_cases hjm : j < m
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hjm, ↓reduceDIte, Option.getD_some] at hj ⊢
    exact hx ⟨j, hjm⟩ hj
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hjm, ↓reduceDIte, Option.getD_none] at hj
    exact (Bool.false_ne_true hj).elim

lemma wires_input {m : ℕ} (gs : List Gate) (x : Fin m → Bool) (v : Fin m) :
    (evalWires gs (List.ofFn x)).getD v.val false = x v := by
  rw [evalWires_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma or_cone_trace {m : ℕ} {gs : List Gate}
    (hao : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin m → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (hnoand : ∀ j < k, ∀ hj : j < gs.length, (gs[j]'hj).op = GateOp.and →
      (evalWires gs (List.ofFn x)).getD (m + j) false = false) :
    ∀ w < m + k, (evalWires gs (List.ofFn x)).getD w false = true →
      ∃ u : Fin m, x u = true ∧
        (evalWires gs (List.ofFn (PEqualNP.EdgeOwnership.pairInput u u))).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwk hwtrue
    by_cases hwm : w < m
    · refine ⟨⟨w, hwm⟩, ?_, ?_⟩
      · have hi := wires_input gs x ⟨w, hwm⟩
        rw [hi] at hwtrue
        exact hwtrue
      · rw [wires_input gs (PEqualNP.EdgeOwnership.pairInput ⟨w, hwm⟩ ⟨w, hwm⟩) ⟨w, hwm⟩]
        simp [PEqualNP.EdgeOwnership.pairInput]
    · set j := w - m with hj_def
      have hw_eq : w = m + j := by omega
      have hjk : j < k := by omega
      have hj : j < gs.length := Nat.lt_of_lt_of_le hjk hk
      rw [hw_eq] at hwtrue ⊢
      rcases (hao (gs[j]'hj) (List.getElem_mem hj)).1 with hand | hor
      · have hf := hnoand j hjk hj hand
        rw [hf] at hwtrue
        exact (Bool.false_ne_true hwtrue).elim
      · have hstep := evalWires_getD_gate gs x j hj
        rw [hstep] at hwtrue
        simp only [gateStep, hor, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hwtrue
        rcases hwtrue with ⟨_, ⟨c, hc, rfl⟩, hctrue⟩
        have hcmj : c < m + j := by
          by_contra hge
          have h1 : (List.ofFn x).length + (gs.take j).length ≤ c := by
            rw [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
          rw [evalWires_getD_ge _ _ c h1] at hctrue
          exact Bool.false_ne_true hctrue
        have hcfull : (evalWires gs (List.ofFn x)).getD c false = true := by
          rw [← evalWires_take_getD gs (List.ofFn x) j c (by rw [List.length_ofFn]; exact hcmj)]
          exact hctrue
        obtain ⟨u, hxu, hcu⟩ := ih c (by omega) (by omega) hcfull
        refine ⟨u, hxu, ?_⟩
        rw [evalWires_getD_gate gs _ j hj]
        simp only [gateStep, hor, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        refine ⟨_, ⟨c, hc, rfl⟩, ?_⟩
        rw [evalWires_take_getD gs _ j c (by rw [List.length_ofFn]; exact hcmj)]
        exact hcu

lemma and_clean_of_pair_clean {m : ℕ} (hm : 0 < m) (H : SimpleGraph (Fin m))
    (D : Circuit)
    (hao : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpair : ∀ k : ℕ, k < D.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = GateOp.and →
      ∀ e w : Fin m, ¬ H.Adj e w →
        PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false)
    (x : Fin m → Bool)
    (hind : ∀ u v : Fin m, H.Adj u v → ¬ (x u = true ∧ x v = true)) :
    ∀ k : ℕ, ∀ hk : k < D.gates.length, (D.gates[k]'hk).op = GateOp.and →
      (evalWires D.gates (List.ofFn x)).getD (m + k) false = false := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hand
    by_contra hne
    have htrue : (evalWires D.gates (List.ofFn x)).getD (m + k) false = true := by
      cases hv : (evalWires D.gates (List.ofFn x)).getD (m + k) false
      · exact (hne hv).elim
      · rfl
    have hgateAt : PEqualNP.MetaComplexity.NestedCover.gateAt D k = D.gates[k]'hk := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk]
    have hstep := evalWires_getD_gate D.gates x k hk
    rw [hstep] at htrue
    have hlen : (D.gates[k]'hk).inputs.length ≤ 2 := (hao _ (List.getElem_mem hk)).2
    have hpair_k : ∀ e w : Fin m, ¬ H.Adj e w →
        (evalWires D.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput e w))).getD (m + k) false = false := by
      intro e w hna
      have hp := hpair k hk (hgateAt ▸ hand) e w hna
      exact hp
    match hinp : (D.gates[k]'hk).inputs with
    | [] =>
      let e0 : Fin m := ⟨0, hm⟩
      have hf := hpair_k e0 e0 (H.loopless.irrefl e0)
      rw [evalWires_getD_gate D.gates _ k hk] at hf
      simp [gateStep, hand, hinp, GateOp.eval] at hf
    | [a] =>
      simp only [gateStep, hand, hinp, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, id_eq] at htrue
      have hamk : a < m + k := by
        by_contra hge
        have h1 : (List.ofFn x).length + (D.gates.take k).length ≤ a := by
          rw [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]; omega
        rw [evalWires_getD_ge _ _ a h1] at htrue
        exact Bool.false_ne_true htrue
      have hafull : (evalWires D.gates (List.ofFn x)).getD a false = true := by
        rw [← evalWires_take_getD D.gates (List.ofFn x) k a (by rw [List.length_ofFn]; exact hamk)]
        exact htrue
      obtain ⟨u, _, hau⟩ := or_cone_trace hao x k (Nat.le_of_lt hk) ih a hamk hafull
      have hf := hpair_k u u (H.loopless.irrefl u)
      rw [evalWires_getD_gate D.gates _ k hk] at hf
      simp only [gateStep, hand, hinp, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, id_eq] at hf
      rw [evalWires_take_getD D.gates _ k a (by rw [List.length_ofFn]; exact hamk)] at hf
      rw [hau] at hf
      exact Bool.false_ne_true hf.symm
    | [a, b] =>
      simp only [gateStep, hand, hinp, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id_eq] at htrue
      rcases htrue with ⟨hat, hbt⟩
      have hamk : a < m + k := by
        by_contra hge
        have h1 : (List.ofFn x).length + (D.gates.take k).length ≤ a := by
          rw [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]; omega
        rw [evalWires_getD_ge _ _ a h1] at hat
        exact Bool.false_ne_true hat
      have hbmk : b < m + k := by
        by_contra hge
        have h1 : (List.ofFn x).length + (D.gates.take k).length ≤ b := by
          rw [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]; omega
        rw [evalWires_getD_ge _ _ b h1] at hbt
        exact Bool.false_ne_true hbt
      have hafull : (evalWires D.gates (List.ofFn x)).getD a false = true := by
        rw [← evalWires_take_getD D.gates (List.ofFn x) k a (by rw [List.length_ofFn]; exact hamk)]
        exact hat
      have hbfull : (evalWires D.gates (List.ofFn x)).getD b false = true := by
        rw [← evalWires_take_getD D.gates (List.ofFn x) k b (by rw [List.length_ofFn]; exact hbmk)]
        exact hbt
      obtain ⟨u, hxu, hau⟩ := or_cone_trace hao x k (Nat.le_of_lt hk) ih a hamk hafull
      obtain ⟨v, hxv, hbv⟩ := or_cone_trace hao x k (Nat.le_of_lt hk) ih b hbmk hbfull
      have hna : ¬ H.Adj u v := fun hadj => hind u v hadj ⟨hxu, hxv⟩
      have hauv : (evalWires D.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD a false = true := by
        apply wires_mono hao _ a hau
        intro z hz
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_iff] at hz ⊢
        rcases hz with rfl | rfl <;> exact Or.inl rfl
      have hbuv : (evalWires D.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD b false = true := by
        apply wires_mono hao _ b hbv
        intro z hz
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_iff] at hz ⊢
        rcases hz with rfl | rfl <;> exact Or.inr rfl
      have hf := hpair_k u v hna
      rw [evalWires_getD_gate D.gates _ k hk] at hf
      simp only [gateStep, hand, hinp, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, id_eq] at hf
      rw [evalWires_take_getD D.gates _ k a (by rw [List.length_ofFn]; exact hamk),
          evalWires_take_getD D.gates _ k b (by rw [List.length_ofFn]; exact hbmk),
          hauv, hbuv] at hf
      exact Bool.false_ne_true hf.symm
    | _ :: _ :: _ :: _ =>
      rw [hinp] at hlen
      simp at hlen

end PEqualNP.Outside.L_meta_1602

theorem PEqualNP.Outside.L_meta_1602 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro hclean m H _ hC4 D hmono hfun hpair
  by_cases hm : m = 0
  · subst hm
    refine ⟨∅, fun y => Fin.elim0 y, ?_⟩
    have hedge : H.edgeFinset = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      induction e using Sym2.ind with
      | _ a b => exact Fin.elim0 a
    rw [hedge]
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hao : ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have h1 := hmono g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1.1, h1.2⟩
    have heval : ∀ x : Fin m → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
      intro x
      have hx := congrFun hfun x
      simpa only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun,
        Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or] using hx
    have hclean_and : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
        (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (m + (i : ℕ)) false = true →
        ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
      intro i x hand htrue
      by_contra hno
      have hind : ∀ u v : Fin m, H.Adj u v → ¬ (x u = true ∧ x v = true) := by
        intro u v hadj ⟨hu, hv⟩
        exact hno ⟨u, v, hadj, hu, hv⟩
      have hf := PEqualNP.Outside.L_meta_1602.and_clean_of_pair_clean hmpos H D hao hpair x hind i.val i.isLt hand
      change (PEqualNP.Outside.L_meta_1602.evalWires D.gates (List.ofFn x)).getD (m + i.val) false = true at htrue
      rw [hf] at htrue
      exact Bool.false_ne_true htrue
    exact hclean m H hC4 D.gates D.output hao heval hclean_and
