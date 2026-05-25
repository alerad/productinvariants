import ProductInvariants.Finite.Monotonicity

namespace ProductInvariants

def truncationSet (A : ℕ → Prop) [DecidablePred A] (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => 0 < n ∧ A n)

theorem truncationSet_mono (A : ℕ → Prop) [DecidablePred A] :
    Monotone (truncationSet A) := by
  intro N M hNM
  unfold truncationSet
  exact Finset.filter_subset_filter _ (Finset.range_mono (Nat.succ_le_succ hNM))

theorem truncation_phaseIntegral_antitone (A : ℕ → Prop) [DecidablePred A] :
    Antitone fun N => phaseIntegral (truncationSet A N) := by
  intro N M hNM
  exact phaseIntegral_antitone (truncationSet_mono A hNM)

/-- Directed phase integral as the infimum of finite truncations. -/
noncomputable def directedPhaseIntegral (A : ℕ → Prop) [DecidablePred A] : ℝ :=
  ⨅ N : ℕ, phaseIntegral (truncationSet A N)

theorem directedPhaseIntegral_eq_iInf (A : ℕ → Prop) [DecidablePred A] :
    directedPhaseIntegral A =
      ⨅ N : ℕ, phaseIntegral (truncationSet A N) := rfl

theorem directedPhaseIntegral_le_truncation
    (A : ℕ → Prop) [DecidablePred A] (N : ℕ) :
    directedPhaseIntegral A ≤ phaseIntegral (truncationSet A N) := by
  exact ciInf_le
    ⟨0, by
      rintro x ⟨M, rfl⟩
      exact phaseIntegral_nonneg (truncationSet A M)⟩
    N

theorem mem_truncationSet_of_pos_le {A : ℕ → Prop} [DecidablePred A]
    {n N : ℕ} (hnpos : 0 < n) (hnA : A n) (hnle : n ≤ N) :
    n ∈ truncationSet A N := by
  unfold truncationSet
  simp [hnpos, hnA, hnle]

theorem directed_one_half_barrier {A : ℕ → Prop} [DecidablePred A]
    (h1 : A 1) :
    directedPhaseIntegral A ≤ (1 : ℝ) / 2 := by
  have hmem : 1 ∈ truncationSet A 1 :=
    mem_truncationSet_of_pos_le (by norm_num) h1 (by norm_num)
  exact (directedPhaseIntegral_le_truncation A 1).trans
    (one_half_barrier hmem)

theorem directed_one_half_barrier_strict_of_exists
    {A : ℕ → Prop} [DecidablePred A]
    (h1 : A 1) {m : ℕ} (hmA : A m) (hmgt : 1 < m) :
    directedPhaseIntegral A < (1 : ℝ) / 2 := by
  have h1mem : 1 ∈ truncationSet A m :=
    mem_truncationSet_of_pos_le (by norm_num) h1 (Nat.le_of_lt hmgt)
  have hmmem : m ∈ truncationSet A m :=
    mem_truncationSet_of_pos_le (lt_trans Nat.zero_lt_one hmgt) hmA le_rfl
  exact lt_of_le_of_lt (directedPhaseIntegral_le_truncation A m)
    (one_half_barrier_strict_of_mem h1mem hmmem hmgt)

theorem directed_one_half_eq_only_one
    {A : ℕ → Prop} [DecidablePred A]
    (h1 : A 1) (heq : directedPhaseIntegral A = (1 : ℝ) / 2)
    {m : ℕ} (hmpos : 0 < m) (hmA : A m) :
    m = 1 := by
  by_contra hne
  have hmgt : 1 < m := by omega
  have hlt := directed_one_half_barrier_strict_of_exists
    (A := A) h1 hmA hmgt
  linarith

end ProductInvariants
