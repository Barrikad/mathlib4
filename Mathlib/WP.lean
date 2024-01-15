import Aesop
import Mathlib.Order.CompleteLattice
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Order.OrdinalApproximantsFixedPoints

open OrdinalApprox
--TODO: better syntax
inductive Prog where
  | havoc : String → Prog
  | assign : String → ((String → Int) → Int) → Prog
  | seq : Prog → Prog → Prog
  | ifte : ((String → Int) → Bool) → Prog → Prog → Prog
  | loop : ((String → Int) → Bool) → Prog → Prog

def wp (c : Prog) : ((String → Int) → Prop) →o ((String → Int) → Prop) :=
  match c with
  | .havoc x =>
    let f q s := ∀ v, q (Function.update s x v)
    let h : Monotone f := by
      intro q₁ q₂ h v h'  _
      apply h
      apply h'
    OrderHom.mk f h
  | .assign x t =>
    let f q s := q (Function.update s x (t s))
    let h : Monotone f := by
      intro q₁ q₂ h v h'
      apply h
      apply h'
    OrderHom.mk f h
  | .seq c1 c2 =>
    let f q := wp c1 (wp c2 q)
    let h : Monotone f := by
      have h1 := OrderHom.monotone' (wp c2)
      have h2 := OrderHom.monotone' (wp c1)
      intro q₁ q₂ h v h'
      apply h2
      on_goal 2 => exact h'
      apply h1
      assumption
    OrderHom.mk f h
  | .ifte b c1 c2 =>
    let f q s := (b s → wp c1 q s) ∧ (¬ b s → wp c2 q s)
    let h : Monotone f := by
      have h1 := OrderHom.monotone' (wp c1)
      have h2 := OrderHom.monotone' (wp c2)
      intro s₁ s₂ h
      intro v
      intro h'
      apply And.intro
      . intro h''
        have := (And.left h' h'')
        simp_all only [forall_true_left, not_true_eq_false, IsEmpty.forall_iff, and_self]
        apply h1
        on_goal 2 => exact this
        assumption
      . intro h''
        have := (And.right h' h'')
        simp_all only [IsEmpty.forall_iff, not_false_eq_true, forall_true_left, and_self, Bool.not_eq_true]
        apply h2
        on_goal 2 => exact this
        assumption
    OrderHom.mk f h
  | .loop b c =>
    let g (q : (String → Int) → Prop) x s :=  (b s → wp c x s) ∧ (¬ b s → q s)
    let hg q : Monotone (g q) := by
      intro x1 x2 h s h'
      apply And.intro
      . intro hb
        exact OrderHom.monotone' (wp c) h s (And.left h' hb)
      . intro hb
        exact And.right h' hb
    let f q := OrderHom.lfp (OrderHom.mk (g q) (hg q))
    let h : Monotone f := by
      intro q₁ q₂ h
      have : g q₁ ≤ g q₂ := by
        intro x s h'
        apply And.intro
        . intro hb
          exact (And.left h') hb
        . intro hb
          have hq := (And.right h') hb
          exact ((h s) hq)
      apply OrderHom.monotone' (OrderHom.lfp : (((String → Int) → Prop) →o ((String → Int) → Prop)) →o (String → Int) → Prop)
      assumption
    OrderHom.mk f h

def phi (b : (String → Int) → Bool) c (q : (String → Int) → Prop) x s := (b s → wp c x s) ∧ (¬ b s → q s)

lemma phi_mono (b : (String → Int) → Bool) (c : Prog) (q : (String → Int) → Prop) : Monotone (phi b c q) := by
  intro x1 x2 h s h'
  apply And.intro
  . intro hb
    exact OrderHom.monotone' (wp c) h s (And.left h' hb)
  . intro hb
    exact And.right h' hb

lemma phi_conjunctive_step b (c : Prog) q₁ q₂ x y z
    (hyp : ∀ q₁ q₂, wp c q₁ ⊓ wp c q₂ ≤ wp c (q₁ ⊓ q₂))
    (h : x ⊓ y ≤ z)
    : phi b c q₁ x ⊓ phi b c q₂ y ≤ phi b c (q₁ ⊓ q₂) z := by
  intro s h'
  apply And.intro
  . intro hb
    exact
      OrderHom.monotone' (wp c) h s
        ((hyp x y s) (And.intro (And.left (And.left h') hb) (And.left (And.right h') hb)))
  . intro hb
    exact And.intro (And.right (And.left h') hb) (And.right (And.right h') hb)

lemma lfp_approx_zero {α : Type} [CompleteLattice α] (f : α →o α) : lfp_approx f 0 = Bot.bot:= by
  unfold lfp_approx
  apply Iff.mpr sSup_eq_bot
  intro a h
  simp_all only [exists_prop, Set.mem_setOf_eq]
  apply Exists.elim h
  intro b h'
  have := And.left h'
  have : ¬ b < 0 := by exact Ordinal.not_lt_zero b
  contradiction

theorem wp_conjunctive (c : Prog) q₁ q₂ : wp c q₁ ⊓ wp c q₂ ≤ wp c (q₁ ⊓ q₂) :=
  match c with
  | .havoc x => by
    intro s h v
    have := And.left h v
    have := And.right h v
    simp_all
    done
  | .assign x f => by
    intro s h
    assumption
  | .seq c₁ c₂ => by
    have h1 := wp_conjunctive c₁ (wp c₂ q₁) (wp c₂ q₂)
    have h2 := OrderHom.monotone' (wp c₁) (wp_conjunctive c₂ q₁ q₂)
    exact ge_trans h2 h1
  | .ifte b c₁ c₂ => by
    intro s h
    apply And.intro
    . intro hb
      exact wp_conjunctive c₁ q₁ q₂ s (And.intro (And.left (And.left h) hb) (And.left (And.right h) hb))
    . intro hb
      exact wp_conjunctive c₂ q₁ q₂ s (And.intro (And.right (And.left h) hb) (And.right (And.right h) hb))
  | .loop b c => by
    let ohmk := fun q' => OrderHom.mk (phi b c q') (phi_mono b c q')
    let phihm := fun q' => lfp_approx (ohmk q')
    have : ∀ a : Ordinal, phihm q₁ a ⊓ phihm q₂ a ≤ phihm (q₁ ⊓ q₂) a := by
      intro a
      induction a using Ordinal.induction with
      | h i IH =>
        have ihj := fun j (h : j < i) =>
          phi_conjunctive_step b c q₁ q₂
            (phihm q₁ j) (phihm q₂ j) (phihm (q₁ ⊓ q₂) j)
            (fun q₁' q₂' => wp_conjunctive c q₁' q₂') (IH j h)
        intro s h
        dsimp [phihm] at h
        unfold lfp_approx at h
        apply Exists.elim
          (Iff.mp
            (unary_relation_sSup_iff
              { (ohmk q₁) (phihm q₁ j) | (j : Ordinal) (_ : j < i) } (a := s))
            (And.left h))
        simp only [OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq, ge_iff_le, and_imp,
          forall_exists_index, forall_apply_eq_imp_iff₂]
        intro j hj hjs
        apply Exists.elim
          (Iff.mp
            (unary_relation_sSup_iff
              { (ohmk q₂) (phihm q₂ j) | (j : Ordinal) (_ : j < i) } (a := s))
            (And.right h))
        simp only [OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq, ge_iff_le, and_imp,
          forall_exists_index, forall_apply_eq_imp_iff₂]
        intro k hk hks
        have jk_le_i : max j k < i := by
          simp_all only [ge_iff_le, OrderHom.coe_mk, exists_prop,
            Set.mem_setOf_eq, max_lt_iff, and_self]
        unfold lfp_approx
        apply Iff.mpr
          (unary_relation_sSup_iff
            { (ohmk (q₁ ⊓ q₂)) (phihm (q₁ ⊓ q₂) j) | (j : Ordinal) (_ : j < i) }
            (a := s))
        apply Exists.intro (phi b c (q₁ ⊓ q₂) (phihm (q₁ ⊓ q₂) (max j k)))
        apply And.intro
        . simp only [ge_iff_le, OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq]
          apply Exists.intro (max j k)
          apply And.intro jk_le_i
          rfl
        . apply ihj (max j k) jk_le_i s
          apply And.intro
          . exact OrderHom.monotone (ohmk q₁)
              (lfp_approx_monotone (ohmk q₁) (le_max_left j k)) s hjs
          . exact OrderHom.monotone (ohmk q₂)
              (lfp_approx_monotone (ohmk q₂) (le_max_right j k)) s hks
    have hbigord := this (Cardinal.ord $ Order.succ (Cardinal.mk ((String → Int) → Prop)))
    intro s h
    apply Eq.mp (congrFun (lfp_is_lfp_approx_cardinal (ohmk (q₁ ⊓ q₂))) s)
    apply hbigord
    apply And.intro
    . exact Eq.mpr (congrFun (lfp_is_lfp_approx_cardinal (ohmk q₁)) s) (And.left h)
    . exact Eq.mpr (congrFun (lfp_is_lfp_approx_cardinal (ohmk q₂)) s) (And.right h)
