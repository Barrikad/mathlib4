import Aesop
import Mathlib.Order.CompleteLattice
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Order.OrdinalApproximantsFixedPoints

open OrdinalApprox

abbrev State := String → Int
abbrev Expr α := State → α

inductive Prog where
  | havoc : String → Prog
  | assign : String → (Expr Int) → Prog
  | seq : Prog → Prog → Prog
  | ifte : (Expr Bool) → Prog → Prog → Prog
  | while : (Expr Bool) → Prog → Prog

def wp (c : Prog) : (State → Prop) →o (State → Prop) :=
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
      have h1 := (wp c2).monotone
      have h2 := (wp c1).monotone
      intro q₁ q₂ h v h'
      apply h2
      on_goal 2 => exact h'
      apply h1
      assumption
    OrderHom.mk f h
  | .ifte b c1 c2 =>
    let f q s := (b s → wp c1 q s) ∧ (¬ b s → wp c2 q s)
    let h : Monotone f := by
      have h1 := (wp c1).monotone
      have h2 := (wp c2).monotone
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
  | .while b c =>
    let g (q : State → Prop) x s :=  (b s → wp c x s) ∧ (¬ b s → q s)
    let hg q : Monotone (g q) := by
      intro x1 x2 h s h'
      apply And.intro
      . intro hb
        exact (wp c).monotone h s (And.left h' hb)
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
      apply (OrderHom.lfp : ((State → Prop) →o (State → Prop)) →o State → Prop).monotone
      assumption
    OrderHom.mk f h

def φ (b : Expr Bool) (c : Prog) (q x : State → Prop) (s : State) :=
  (b s → wp c x s) ∧ (¬ b s → q s)

lemma φ_mono (b : Expr Bool) (c : Prog) (q : State → Prop) : Monotone (φ b c q) := by
  intro x1 x2 h s h'
  have := (wp c).monotone
  cases h'
  apply And.intro
  all_goals aesop

lemma φ_conjunctive_step b (c : Prog) q₁ q₂ x y z
    (hyp : ∀ q₁ q₂, wp c q₁ ⊓ wp c q₂ ≤ wp c (q₁ ⊓ q₂))
    (h : x ⊓ y ≤ z)
    : φ b c q₁ x ⊓ φ b c q₂ y ≤ φ b c (q₁ ⊓ q₂) z := by
  intro s h'
  cases h'; rename_i l r; cases l; cases r
  constructor <;> intro _
  on_goal 1 =>
    apply (wp c).monotone h s
    apply hyp x y s
  all_goals constructor <;> simp_all only [ge_iff_le, IsEmpty.forall_iff,
    not_false_eq_true, forall_true_left, Bool.not_eq_true]

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
    have h2 := (wp c₁).monotone (wp_conjunctive c₂ q₁ q₂)
    exact ge_trans h2 h1
  | .ifte b c₁ c₂ => by
    intro s h
    apply And.intro
    . intro hb
      exact wp_conjunctive c₁ q₁ q₂ s (And.intro (And.left (And.left h) hb) (And.left (And.right h) hb))
    . intro hb
      exact wp_conjunctive c₂ q₁ q₂ s (And.intro (And.right (And.left h) hb) (And.right (And.right h) hb))
  | .while b c => by
    let ohmk q' := OrderHom.mk (φ b c q') (φ_mono b c q')
    let φhm q' := lfp_approx (ohmk q')
    have : ∀ a : Ordinal, φhm q₁ a ⊓ φhm q₂ a ≤ φhm (q₁ ⊓ q₂) a := by
      intro a
      induction a using Ordinal.induction with
      | h i IH =>
        have ihj := fun j (h : j < i) =>
          φ_conjunctive_step b c q₁ q₂
            (φhm q₁ j) (φhm q₂ j) (φhm (q₁ ⊓ q₂) j)
            (fun q₁' q₂' => wp_conjunctive c q₁' q₂') (IH j h)
        intro s h
        dsimp [φhm] at h
        unfold lfp_approx at h
        apply Exists.elim
          (Iff.mp
            (unary_relation_sSup_iff
              { (ohmk q₁) (φhm q₁ j) | (j : Ordinal) (_ : j < i) } (a := s))
            (And.left h))
        simp only [OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq, ge_iff_le, and_imp,
          forall_exists_index, forall_apply_eq_imp_iff₂]
        intro j hj hjs
        apply Exists.elim
          (Iff.mp
            (unary_relation_sSup_iff
              { (ohmk q₂) (φhm q₂ j) | (j : Ordinal) (_ : j < i) } (a := s))
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
            { (ohmk (q₁ ⊓ q₂)) (φhm (q₁ ⊓ q₂) j) | (j : Ordinal) (_ : j < i) }
            (a := s))
        apply Exists.intro (φ b c (q₁ ⊓ q₂) (φhm (q₁ ⊓ q₂) (max j k)))
        apply And.intro
        . simp only [ge_iff_le, OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq]
          apply Exists.intro (max j k)
          apply And.intro jk_le_i
          rfl
        . apply ihj (max j k) jk_le_i s
          apply And.intro
          . exact (ohmk q₁).monotone
              (lfp_approx_monotone (ohmk q₁) (le_max_left j k)) s hjs
          . exact (ohmk q₂).monotone
              (lfp_approx_monotone (ohmk q₂) (le_max_right j k)) s hks
    have hbigord := this (Cardinal.ord $ Order.succ (Cardinal.mk (State → Prop)))
    intro s h
    apply Eq.mp (congrFun (lfp_is_lfp_approx_cardinal (ohmk (q₁ ⊓ q₂))) s)
    apply hbigord
    apply And.intro
    . exact Eq.mpr (congrFun (lfp_is_lfp_approx_cardinal (ohmk q₁)) s) (And.left h)
    . exact Eq.mpr (congrFun (lfp_is_lfp_approx_cardinal (ohmk q₂)) s) (And.right h)
