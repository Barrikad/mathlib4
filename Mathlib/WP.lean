import Aesop
import Mathlib.Order.CompleteLattice
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Order.OrdinalApproximantsFixedPoints

open OrdinalApprox

inductive Prog where
  | havoc : String → Prog
  | assign : String → ((String → Int) → Int) → Prog
  | seq : Prog → Prog → Prog
  | ifte : ((String → Int) → Bool) → Prog → Prog → Prog
  | loop : ((String → Int) → Bool) → Prog → Prog

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α := sInf { x | f x ≤ x }

lemma lfp_mono {α : Type} [CompleteLattice α]: Monotone (lfp : (α → α) → α) := by
  intro f g h
  have h' : { x | g x ≤ x } ⊆ { x | f x ≤ x } := by
    intro x
    intro h'
    have := ge_trans h' (h x)
    assumption
  exact sInf_le_sInf h'

theorem lfp_OrderHom {α : Type} [CompleteLattice α] {f : α → α} {h : Monotone f} : lfp f = OrderHom.lfp (OrderHom.mk f h) := rfl

def wp (c : Prog) (q : (String → Int) → Prop) : (String → Int) → Prop :=
  match c with
  | .havoc x => λ s ↦ ∀ v, q (Function.update s x v)
  | .assign x f => λ s ↦ q (Function.update s x (f s))
  | .seq c1 c2 => wp c1 (wp c2 q)
  | .ifte b c1 c2 => λ s ↦ (b s → wp c1 q s) ∧ (¬ b s → wp c2 q s)
  | .loop b c => lfp (λ x ↦ (λ s ↦ (b s → wp c x s) ∧ (¬ b s → q s)))

def phi (b : (String → Int) → Bool) (c : Prog) (q : (String → Int) → Prop) x := (λ s ↦ (b s → wp c x s) ∧ (¬ b s → q s))

lemma wp_mono (c : Prog) : Monotone (wp c) :=
  match c with
  | .havoc x => by
    intro q₁ q₂ h v h'  _
    apply h
    apply h'
  | .assign x f => by
    intro q₁ q₂ h v h'
    apply h
    apply h'
  | .seq c1 c2 => by
    have h1 := wp_mono c2
    have h2 := wp_mono c1
    intro q₁ q₂ h v h'
    apply h2
    on_goal 2 => exact h'
    apply h1
    simp_all only
    done
  | .ifte b c1 c2 => by
    have h1 := wp_mono c1
    have h2 := wp_mono c2
    intro s₁ s₂ h
    unfold wp
    intro v
    intro h'
    apply And.intro
    . intro h''
      have := (And.left h' h'')
      simp_all only [forall_true_left, not_true_eq_false, IsEmpty.forall_iff, and_self]
      apply h1
      on_goal 2 => exact this
      simp_all only
      done
    . intro h''
      have := (And.right h' h'')
      simp_all only [IsEmpty.forall_iff, not_false_eq_true, forall_true_left, and_self, Bool.not_eq_true]
      apply h2
      on_goal 2 => exact this
      simp_all only
      done
  | .loop b c => by
    intro q₁ q₂ h
    have : phi b c q₁ ≤ phi b c q₂ := by
      intro x s h'
      apply And.intro
      . intro hb
        exact (And.left h') hb
      . intro hb
        have hq := (And.right h') hb
        exact ((h s) hq)
    exact lfp_mono this

lemma phi_mono (b : (String → Int) → Bool) (c : Prog) (q : (String → Int) → Prop) : Monotone (phi b c q) := by
  intro x1 x2 h s h'
  apply And.intro
  . intro hb
    exact wp_mono c h s (And.left h' hb)
  . intro hb
    exact And.right h' hb

lemma phi_conjunctive_step (b : (String → Int) → Bool) (c : Prog) (q₁ q₂ x y z : (String → Int) → Prop)
  (hyp : ∀ q₁ q₂, wp c q₁ ⊓ wp c q₂ ≤ wp c (q₁ ⊓ q₂)) (h : x ⊓ y ≤ z) : phi b c q₁ x ⊓ phi b c q₂ y ≤ phi b c (q₁ ⊓ q₂) z := by
  intro s h'
  apply And.intro
  . intro hb
    exact wp_mono c h s ((hyp x y s) (And.intro (And.left (And.left h') hb) (And.left (And.right h') hb)))
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

theorem wp_conjunctive (c : Prog) (q₁ : (String → Int) → Prop) (q₂ : (String → Int) → Prop) : wp c q₁ ⊓ wp c q₂ ≤ wp c (q₁ ⊓ q₂) :=
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
    have h2 := wp_mono c₁ (wp_conjunctive c₂ q₁ q₂)
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
        have ihj := fun j (h : j < i) => phi_conjunctive_step b c q₁ q₂ (phihm q₁ j) (phihm q₂ j) (phihm (q₁ ⊓ q₂) j) (fun q₁' q₂' => wp_conjunctive c q₁' q₂') (IH j h)
        intro s h
        dsimp [phihm] at h
        unfold lfp_approx at h
        apply Exists.elim (Iff.mp (unary_relation_sSup_iff { (ohmk q₁) (phihm q₁ j) | (j : Ordinal) (_ : j < i) } (a := s)) (And.left h))
        simp only [OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq, ge_iff_le, and_imp,
          forall_exists_index, forall_apply_eq_imp_iff₂]
        intro j hj hjs
        apply Exists.elim (Iff.mp (unary_relation_sSup_iff { (ohmk q₂) (phihm q₂ j) | (j : Ordinal) (_ : j < i) } (a := s)) (And.right h))
        simp only [OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq, ge_iff_le, and_imp,
          forall_exists_index, forall_apply_eq_imp_iff₂]
        intro k hk hks
        have jk_le_i : max j k < i := by
          simp_all only [ge_iff_le, OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq, max_lt_iff, and_self]
        unfold lfp_approx
        apply Iff.mpr (unary_relation_sSup_iff { (ohmk (q₁ ⊓ q₂)) (phihm (q₁ ⊓ q₂) j) | (j : Ordinal) (_ : j < i) } (a := s))
        apply Exists.intro (phi b c (q₁ ⊓ q₂) (phihm (q₁ ⊓ q₂) (max j k)))
        apply And.intro
        . simp only [ge_iff_le, OrderHom.coe_mk, exists_prop, Set.mem_setOf_eq]
          apply Exists.intro (max j k)
          apply And.intro jk_le_i
          rfl
        . apply ihj (max j k) jk_le_i s
          apply And.intro
          . exact OrderHom.monotone (ohmk q₁) (lfp_approx_monotone (ohmk q₁) (le_max_left j k)) s hjs
          . exact OrderHom.monotone (ohmk q₂) (lfp_approx_monotone (ohmk q₂) (le_max_right j k)) s hks
    have hbigord := this (Cardinal.ord $ Order.succ (Cardinal.mk ((String → Int) → Prop)))
    intro s h
    apply Eq.mpr (congrFun lfp_OrderHom s)
    apply Eq.mp (congrFun (lfp_is_lfp_approx_cardinal (ohmk (q₁ ⊓ q₂))) s)
    apply hbigord
    apply And.intro
    . apply Eq.mpr (congrFun (lfp_is_lfp_approx_cardinal (ohmk q₁)) s)
      apply Eq.mp (congrFun (lfp_OrderHom (f := phi b c q₁)) s)
      exact And.left h
    . apply Eq.mpr (congrFun (lfp_is_lfp_approx_cardinal (ohmk q₂)) s)
      apply Eq.mp (congrFun (lfp_OrderHom (f := phi b c q₂)) s)
      exact And.right h
    done
