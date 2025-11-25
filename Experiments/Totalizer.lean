import Trestle.Encode.Cardinality.Defs
import Trestle.Solver.Dimacs

namespace List

-- By Kenny Lau
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/List.20length.20induction/near/554091009
theorem length_wf {α : Type} : WellFounded (λ (x y : List α) ↦ x.length < y.length) := InvImage.wf _ Nat.lt_wfRel.2

def length_induction {α : Type} := @WellFounded.induction (List α) _ length_wf

end List

namespace Trestle.Encode.Cardinality

open EncCNF Model PropFun

def totalizer [LE ν] [DecidableLE ν] [HAdd ν ℕ ν] {k : ℕ} (c : Vector (Literal ν) k) (nextVar : ν) : Array (Clause (Literal ν)) × Vector (Literal ν) k × Option ν :=
match h:c with
| Vector.mk carr _ => match carr with
  | Array.mk clist => match clist with
    | [] => ⟨#[], ⟨⟨[]⟩, by simp_all⟩, none⟩
    | x :: [] => ⟨#[], ⟨#[x], by simp_all⟩, none⟩
    | x :: (y :: t) =>
      let ltot := totalizer (@Vector.mk (Literal ν) ((x :: (y :: t)).length / 2) ⟨(x :: (y :: t)).take ((x :: (y :: t)).length / 2)⟩ (by simp; omega)) (nextVar + c.size);
      let rtot := totalizer (@Vector.mk (Literal ν) ((x :: (y :: t)).length - (x :: (y :: t)).length / 2) ⟨(x :: (y :: t)).drop ((x :: (y :: t)).length / 2)⟩ (by simp)) (Option.getD ltot.snd.snd (nextVar + c.size));
      let newVars := List.map (λ n ↦ nextVar + n) (List.range c.size);
  ⟨ltot.fst ++ rtot.fst
++ ⟨List.flatten ((List.finRange ltot.snd.fst.size.succ).map (Fin.cases ((List.finRange rtot.snd.fst.size.succ).filterMap (Fin.cases none (λ j ↦ some #[LitVar.negate (rtot.snd.fst.get j), Literal.pos (newVars.get ⟨j.val, by next klen => simp [← Array.length_toList] at klen; simp [newVars, h, Vector.size, ← klen]; have jlt := j.prop; simp only [rtot] at jlt; trans t.length + 1 + 1 - (t.length + 1 + 1) / 2; assumption; simp⟩)]))) (λ i ↦ (List.finRange rtot.snd.fst.size.succ).map (Fin.cases (#[LitVar.negate (ltot.snd.fst.get i), Literal.pos (newVars.get ⟨i.val, by next klen => simp [← Array.length_toList] at klen; simp [newVars, h, Vector.size, ← klen]; have ilt := i.prop; simp [-Fin.is_lt, ltot] at ilt; trans (t.length + 1 + 1) / 2; assumption; omega⟩)]) (λ j ↦ #[LitVar.negate (ltot.snd.fst.get i), LitVar.negate (rtot.snd.fst.get j), Literal.pos (newVars.get ⟨(i.val + j.val).succ, by next klen => simp [newVars, h, Vector.size, ← klen]; have ilt := i.prop; simp [-Fin.is_lt, ltot, Vector.size] at ilt; have jlt := j.prop; simp [-Fin.is_lt, Vector.size, rtot] at jlt; rw [Nat.lt_iff_le_pred] at jlt; have ijlt := Nat.add_lt_add_of_lt_of_le ilt jlt; rw [← Nat.add_sub_assoc] at ijlt; simp +arith at ijlt; rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left] at ijlt; exact ijlt; omega; omega; omega⟩)])))))⟩
++ ⟨List.flatten ((List.finRange ltot.snd.fst.size.succ).map (Fin.cases ((List.finRange rtot.snd.fst.size.succ).filterMap (Fin.cases none (λ j ↦ some #[rtot.snd.fst.get j, Literal.neg (newVars.get ⟨j.val + ltot.snd.fst.size, by next klen => simp +arith [newVars, h, Vector.size, ← klen]; have jlt := j.prop; simp +arith [ltot, Nat.lt_sub_iff_add_lt] at jlt; assumption⟩)]))) (λ i ↦ (List.finRange rtot.snd.fst.size.succ).map (Fin.cases (#[ltot.snd.fst.get i, Literal.neg (newVars.get ⟨i.val + rtot.snd.fst.size, by next klen => simp +arith [newVars, h, Vector.size, ← klen]; rw [← Nat.add_sub_assoc, Nat.sub_le_iff_le_add]; have ilt := i.prop; simp +arith [Vector.size, ltot] at ilt ⊢; assumption; omega⟩)]) (λ j ↦ #[ltot.snd.fst.get i, rtot.snd.fst.get j, Literal.neg (newVars.get ⟨i.val + j.val, by next klen => simp [newVars, h, Vector.size, ← klen]; have ilt := i.prop; simp +arith [Vector.size, ltot] at ilt; have jlt := j.prop; simp +arith [Vector.size, rtot] at jlt; have ijlt := Nat.add_lt_add_of_le_of_lt ilt jlt; rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left] at ijlt; trans t.length + 1; assumption; simp; omega⟩)])))))⟩
, ⟨@Vector.mk _ c.size ⟨newVars⟩ (by simp [newVars, -List.pure_def, -List.bind_eq_flatMap, List.size_toArray]), Option.getD rtot.snd.snd (nextVar + c.size)⟩⟩
termination_by c.size
decreasing_by
next klen =>
  simp [h, Vector.size, ← klen]
  omega
next klen =>
  simp [h, Vector.size, ← klen]
next absurd _ _ _ =>
  simp +arith [Nat.lt_div_iff_mul_lt] at absurd
  cases t with
  | nil => simp +arith at absurd
  | cons h t' => simp +arith at absurd
next absurd _ _ _ =>
  simp +arith [Nat.le_div_iff_mul_le] at absurd
next absurd _ _ _ =>
  simp +arith [Nat.lt_div_iff_mul_lt] at absurd
  cases t with
  | nil => simp +arith at absurd
  | cons h t' => simp +arith at absurd
next absurd _ _ _ =>
  simp +arith [Nat.sub_eq_zero_iff_le, Nat.le_div_iff_mul_le] at absurd
next absurd _ _ _ =>
  simp +arith [Nat.lt_div_iff_mul_lt] at absurd
  cases t with
  | nil => simp +arith at absurd
  | cons h t' => simp +arith at absurd

-- #eval totalizer (@Vector.mk (Literal ℕ) 0 #[] (by simp)) 1
-- #eval totalizer (@Vector.mk (Literal ℕ) 1 #[Literal.pos 1] (by simp)) 2
-- #eval totalizer (@Vector.mk (Literal ℕ) 2 #[Literal.pos 1, Literal.neg 2] (by simp)) 3
#eval IO.print (Solver.Dimacs.formatFormula (Array.map (λ c ↦ c.map ILit (λ l ↦ l)) (totalizer (@Vector.mk (Literal IVar) 2 #[Literal.pos 1, Literal.pos 2] (by simp)) 3).fst))
-- #eval totalizer (@Vector.mk (Literal ℕ) 3 #[Literal.pos 1, Literal.neg 2, Literal.pos 3] (by simp)) 4
-- #eval (totalizer (@Vector.mk (Literal IVar) 3 #[Literal.pos 1, Literal.neg 2, Literal.pos 3] (by simp)) 4).snd.fst
#eval IO.print (Solver.Dimacs.formatFormula (Array.map (λ c ↦ c.map ILit (λ l ↦ l)) (totalizer (@Vector.mk (Literal IVar) 3 #[Literal.pos 1, Literal.pos 2, Literal.pos 3] (by simp)) 4).fst))

lemma totalizer_works1 : ∀ τ (a : Literal IVar) (m : IVar), let tot := totalizer (@Vector.mk (Literal IVar) 1 #[a] (by simp)) m; (∀ c ∈ tot.fst, ∃ l ∈ c, eval τ l) → card (Multiset.ofList [a]) τ = card (Multiset.ofList tot.snd.fst.toList) τ := by simp [totalizer]

lemma totalizer_works2 : ∀ (τ : PropAssignment IVar) (a b : Literal IVar) (m : IVar), let tot := totalizer (@Vector.mk (Literal IVar) 2 #[a, b] (by simp)) m; (∀ c ∈ tot.fst, ∃ l ∈ c, eval τ l) → tot.snd.fst.map (λ (l : Literal IVar) ↦ eval τ l) = ⟨Array.replicate (card (Multiset.ofList [a, b]) τ) true ++ Array.replicate (2 - card (Multiset.ofList [a,b]) τ) false, by simp; rw [← Nat.add_sub_assoc]; simp; split <;> split <;> simp⟩ := by
  simp [totalizer, Vector.size]
  intros τ a b m sat
  simp [Fin.exists_fin_succ] at sat
  split
  next atrue =>
    simp [SemanticEntails.entails, satisfies] at atrue
    have m0 := sat #[-a, LitVar.mkPos (m + 0)]
    simp at m0
    simp [atrue] at m0
    split
    next btrue =>
      simp [SemanticEntails.entails, satisfies] at btrue
      simp [List.range, List.range.loop]
      have m1 := sat #[-a, -b, LitVar.mkPos (m + 1)]
      simp [atrue, btrue] at m1
      tauto
    next bfalse =>
      simp [SemanticEntails.entails, satisfies] at bfalse
      simp [List.range, List.range.loop]
      have m1 := sat #[b, LitVar.mkNeg (m + 1)]
      simp [atrue, bfalse] at m1
      tauto
  next afalse =>
    simp [SemanticEntails.entails, satisfies] at afalse
    have m1 := sat #[a, LitVar.mkNeg (m + 1)]
    simp [afalse] at m1
    split
    next btrue =>
      simp [SemanticEntails.entails, satisfies] at btrue
      simp [List.range, List.range.loop]
      have m0 := sat #[-b, LitVar.mkPos (m + 0)]
      simp [btrue] at m0
      tauto
    next bfalse =>
      simp [SemanticEntails.entails, satisfies] at bfalse
      simp [List.range, List.range.loop]
      have m0 := sat #[a, b, LitVar.mkNeg (m + 0)]
      simp [afalse, bfalse] at m0
      tauto

-- NOTE: How is this possibly missing?
lemma pred_add : ∀ {a b : ℕ}, 0 < b → a + b.pred = (a + b).pred := by
  intros a b
  cases b <;> simp

lemma split_sum : ∀ {A B c : ℕ}, c < A + B → A ≤ c → B ≤ c → ∃ a b, c = (a + b).succ ∧ a < A ∧ b < B := by
  intros A B c cltAB Alec Blec
  have Apos := Nat.lt_of_le_of_lt (Nat.add_le_add_left Blec A) (Nat.add_lt_add_left cltAB A)
  simp at Apos
  have cpos := Nat.lt_of_lt_of_le Apos Alec
  use A.pred, (c.pred - A.pred)
  rw [Nat.add_sub_cancel' (Nat.pred_le_pred Alec), Nat.sub_lt_iff_lt_add, Nat.succ_pred (Nat.ne_of_gt cpos)]
  simp [-Nat.pred_eq_sub_one, Nat.pred_lt_self Apos, pred_add Apos]
  apply Nat.pred_lt_pred (Nat.ne_of_gt cpos)
  · rw [Nat.add_comm]
    assumption
  · apply Nat.pred_le_pred
    assumption

lemma split_sum' : ∀ {A B c : ℕ}, c < A + B → ∃ a b, a + b = c ∧ ((a ≤ A ∧ b < B) ∨ (a < A ∧ b ≤ B))  := by
  intros A B c cltAB
  cases Nat.decLt c (max A B) with
  | isTrue cltmax =>
    simp at cltmax
    cases cltmax with
    | inl cltA =>
      use c, 0
      simp [cltA]
    | inr cleqB =>
      use 0, c
      simp [cleqB]
  | isFalse cgtmax =>
    simp at cgtmax
    use A, (c - A)
    simp [cgtmax.left, Nat.sub_lt_iff_lt_add]
    rw [Nat.add_comm]
    assumption

lemma bounded_sum : ∀ {A B M N c : ℕ}, A + B ≤ c → c < M + N → A ≤ M → B ≤ N → ∃ a b, (A + a) + (B + b) = c ∧ (((A + a ≤ M) ∧ (B + b < N)) ∨ ((A + a < M) ∧ (B + b ≤ N))) := by
  intros A B M N c cgeAB cltMN AleM BleN
  rw [← Nat.sub_lt_sub_iff_right cgeAB, Nat.sub_add_eq (M + N), Nat.sub_add_comm AleM, Nat.add_sub_assoc BleN] at cltMN
  obtain ⟨a, b, absum⟩ := split_sum' cltMN
  use a, b
  omega

set_option maxHeartbeats 500000

lemma totalizer_works : ∀ {k : ℕ} (τ : PropAssignment IVar) (l : Vector (Literal IVar) k) (m : IVar), let tot := totalizer l m; (∀ c ∈ tot.fst, ∃ l ∈ c, eval τ l) → tot.snd.fst.map (λ (l : Literal IVar) ↦ eval τ l) = ⟨Array.replicate (card (Multiset.ofList l.toArray.toList) τ) true ++ Array.replicate (k - card (Multiset.ofList l.toArray.toList) τ) false, by simp; rw [← Nat.add_sub_assoc]; simp; simp [card]; trans l.size; apply Vector.countP_le_size; simp⟩ := by
  intros k τ v
  cases v with
  | mk a asize =>
    cases a with
    | mk l =>
      induction l using List.length_induction generalizing k with
      | h l ih =>
          cases k with
          | zero =>
            simp at asize
            simp [totalizer, asize, card]
          | succ n =>
            cases n with
            | zero =>
              simp at asize
              rw [List.length_eq_one_iff] at asize
              obtain ⟨x, ax⟩ := asize
              simp [ax, totalizer, SemanticEntails.entails, satisfies]
              split <;> simp
              next _ => assumption
              next h =>
                simp at h
                assumption
            | succ m =>
              intro mvar t sat
              simp at asize
              obtain ⟨x, ⟨xt, xl⟩⟩ := List.exists_cons_of_length_eq_add_one asize
              simp [xl] at asize
              obtain ⟨y, ⟨w, yl⟩⟩ := List.exists_cons_of_length_eq_add_one asize
              simp [yl] at xl
              simp [xl, t, totalizer, Vector.size, -List.pure_def, -List.bind_eq_flatMap, -card_cons]
              simp at ih
              simp [t, xl, totalizer, Vector.size, Fin.exists_fin_succ] at sat
              have takeih := @ih (List.take ((w.length + 1 + 1) / 2) (x :: y :: w)) (by simp [xl]; omega) ((w.length + 1 + 1) / 2) (by simp; omega) (mvar + (m + 1 + 1)) (by intro c cmem; have csat := sat c; simp [cmem] at csat; assumption)
              have dropih := @ih (List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)) (by simp [xl]) (w.length + 1 + 1 - (w.length + 1 + 1) / 2) (by simp) ((totalizer (@Vector.mk (Literal IVar) ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1))) (by intro c cmem; have csat := sat c; simp [cmem] at csat; assumption)
              apply List.ext_get
              · simp +arith [-List.pure_def, -List.bind_eq_flatMap, card]
                rw [← Nat.add_sub_assoc]
                · simp
                · apply Nat.le_trans List.countP_le_length
                  simp [yl] at asize
                  simp [asize]
              · simp +arith [-List.pure_def, -List.bind_eq_flatMap, -card_cons]
                intros k kle klt
                rw [List.getElem_append]
                have card_sum : card ↑(x :: y :: w) τ = card ↑(List.take ((w.length + 1 + 1) / 2) (x :: y :: w)) τ + card ↑(List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)) τ := by
                  suffices takedrop : x :: y :: w = List.take ((w.length + 1 + 1) / 2) (x :: y :: w) ++ List.drop ((w.length + 1 + 1) / 2) (x :: y :: w) by
                    rw [takedrop, card_append]
                    simp [-card_cons]
                  simp
                split
                next kltcard =>
                  simp [-card_cons, card_sum] at kltcard ⊢
                  cases Nat.decLt k (max (card ↑(List.take ((w.length + 1 + 1) / 2) (x :: y :: w)) τ) (card ↑(List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)) τ)) with
                  | isTrue kor =>
                    simp at kor
                    cases kor with
                    | inl kltleft =>
                      have fit := sat #[-(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨k, by simp [card] at kltleft; have klt2 := Nat.lt_of_lt_of_le kltleft List.countP_le_length; simp at klt2; exact klt2.left⟩, LitVar.mkPos (mvar + k)]
                      simp at fit
                      rw [← Bool.not_eq_true, ← Decidable.imp_iff_not_or] at fit
                      apply fit
                      · right; right; left
                        use (List.finRange (w.length + 1 + 1 - (w.length + 1 + 1) / 2 + 1)).map (λ i_1 ↦ Fin.cases #[-(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨k, by have klt2 := Nat.lt_of_lt_of_le kltleft List.countP_le_length; simp at klt2; exact klt2.left⟩, LitVar.mkPos (mvar + k)] (λ j ↦ #[-(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨k, by have klt2 := Nat.lt_of_lt_of_le kltleft List.countP_le_length; simp at klt2; exact klt2.left⟩, -(totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.get j, LitVar.mkPos (mvar + (k + j.val + 1))]) i_1)
                        simp
                        apply And.intro
                        · right
                          use ⟨k, by have klt2 := Nat.lt_of_lt_of_le kltleft List.countP_le_length; simp at klt2; exact klt2.left⟩
                          simp
                        · use 0
                          simp
                      · have evalk := congr_arg (λ a ↦ Array.getD a k true) takeih
                        simp [Array.getD] at evalk
                        split at evalk <;> split at evalk
                        next =>
                          simp [Array.getElem_append] at evalk
                          simp [Vector.get, evalk]
                          exact kltleft
                        next _ absurd =>
                          rw [Nat.add_sub_cancel'] at absurd
                          · contradiction
                          · apply Nat.le_trans List.countP_le_length (by simp)
                        next _ absurd =>
                          rw [Nat.add_sub_cancel'] at absurd
                          · contradiction
                          · apply Nat.le_trans List.countP_le_length (by simp)
                        next kge _ =>
                          have absurd := Nat.lt_of_lt_of_le kltleft List.countP_le_length
                          simp at absurd
                          cases kge absurd.left
                    | inr kltright =>
                      -- TODO: Copy and adjust from above (or use wlog)
                      sorry
                  | isFalse kge =>
                    simp at kge
                    obtain ⟨i, j, ⟨kijsucc, ⟨iltleft, jltright⟩⟩⟩ := split_sum kltcard kge.left kge.right
                    have fit := sat #[-(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨i, by simp [card] at iltleft; have klt2 := Nat.lt_of_lt_of_le iltleft List.countP_le_length; simp at klt2; exact klt2.left⟩, -(totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.get ⟨j, by simp [card] at jltright; have klt2 := Nat.lt_of_lt_of_le jltright List.countP_le_length; simp at klt2; exact klt2⟩, LitVar.mkPos (mvar + (i + j + 1))]
                    simp at fit
                    simp [kijsucc]
                    rw [← Bool.not_eq_true, ← Bool.not_eq_true, ← Decidable.imp_iff_not_or, ← Decidable.imp_iff_not_or] at fit
                    apply fit
                    · right; right; left
                      use (List.finRange (w.length + 1 + 1 - (w.length + 1 + 1) / 2 + 1)).map (λ i_1 ↦ Fin.cases #[-(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨i, sorry⟩, LitVar.mkPos (mvar + i)] (λ j ↦ #[-(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨i, sorry⟩, -(totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.get j, LitVar.mkPos (mvar + (i + j.val + 1))])
                i_1)
                      simp
                      apply And.intro
                      · right
                        use ⟨i, sorry⟩
                        simp
                      · use (⟨j, sorry⟩ : Fin _).succ
                        simp
                    · have evalk := congr_arg (λ a ↦ Array.getD a i true) takeih
                      simp [Array.getD] at evalk
                      split at evalk <;> split at evalk
                      next =>
                        simp [Array.getElem_append] at evalk
                        simp [Vector.get, evalk]
                        exact iltleft
                      next _ absurd =>
                        rw [Nat.add_sub_cancel'] at absurd
                        · contradiction
                        · apply Nat.le_trans List.countP_le_length (by simp)
                      next _ absurd =>
                        rw [Nat.add_sub_cancel'] at absurd
                        · contradiction
                        · apply Nat.le_trans List.countP_le_length (by simp)
                      next kge _ =>
                        have absurd := Nat.lt_of_lt_of_le iltleft List.countP_le_length
                        simp at absurd
                        cases kge absurd.left
                    · have evalk := congr_arg (λ a ↦ Array.getD a j true) dropih
                      simp [Array.getD] at evalk
                      split at evalk <;> split at evalk
                      next =>
                        simp [Array.getElem_append] at evalk
                        simp [Vector.get, evalk]
                        exact jltright
                      next _ absurd =>
                        rw [Nat.add_sub_cancel'] at absurd
                        · contradiction
                        · apply Nat.le_trans List.countP_le_length (by simp)
                      next _ absurd =>
                        rw [Nat.add_sub_cancel'] at absurd
                        · contradiction
                        · apply Nat.le_trans List.countP_le_length (by simp)
                      next kge _ =>
                        have absurd := Nat.lt_of_lt_of_le jltright List.countP_le_length
                        simp at absurd
                        cases kge absurd
                next kgecard =>
                  simp [-card_cons, card_sum] at kgecard ⊢
                  have kltcase : ∀ {a b : ℕ}, k = a + b → (card (Multiset.ofList (List.take ((w.length + 1 + 1) / 2) (x :: y :: w))) τ) ≤ a → (card (Multiset.ofList (List.drop ((w.length + 1 + 1) / 2) (x :: y :: w))) τ) ≤ b → a < (totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.size → b < (totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.size → τ (mvar + k) = false := by
                    intro a b kadd alb blb aub bub
                    simp [Vector.size] at aub bub
                    have fit := sat #[(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨a, by apply Nat.lt_of_le_of_lt _ aub; simp +arith [kadd]⟩, (totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.get ⟨b, by apply Nat.lt_of_le_of_lt _ bub; simp +arith [kadd]⟩, LitVar.mkNeg (mvar + (a + b))]
                    simp [← kadd] at fit ⊢
                    rw [← Bool.not_eq_false, ← Bool.not_eq_false, ← Decidable.imp_iff_not_or, ← Decidable.imp_iff_not_or] at fit
                    apply fit
                    · right; right; right
                      use (List.finRange (w.length + 1 + 1 - (w.length + 1 + 1) / 2 + 1)).map (λ j ↦ Fin.cases #[(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨a, by apply Nat.lt_of_le_of_lt _ aub; simp +arith [kadd]⟩, LitVar.mkNeg (mvar + (a + (w.length + 1 + 1 - (w.length + 1 + 1) / 2)))] (λ j ↦  #[(totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.get ⟨a, by apply Nat.lt_of_le_of_lt _ aub; simp +arith [kadd]⟩, (totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.get j, LitVar.mkNeg (mvar + (a + j.val))]) j)
                      apply And.intro
                      · right
                        use ⟨a, by apply Nat.lt_of_le_of_lt _ aub; simp +arith [kadd]⟩
                      · simp
                        use (⟨b, by apply Nat.lt_of_le_of_lt _ bub; simp +arith [kadd]⟩ : Fin _).succ
                        simp [kadd, ← Nat.add_assoc]
                    · have evalk := congr_arg (λ x ↦ Array.getD x a true) takeih
                      simp [Array.getD] at evalk
                      split at evalk
                      next cardlt =>
                        simp [Array.getElem_append] at evalk
                        rw [← Nat.add_sub_assoc] at evalk
                        · simp [cardlt, ← Nat.not_le, alb] at evalk
                          exact evalk
                        · simp [-card_cons, card]
                          trans ((x :: y :: w).take ((w.length + 1 + 1) / 2)).length
                          apply List.countP_le_length
                          simp
                      next _ cardge =>
                        rw [Nat.not_lt] at cardge
                        have absurd : (w.length + 1 + 1) / 2 < (w.length + 1 + 1) / 2 := Nat.lt_of_le_of_lt (Nat.le_trans cardge (by simp +arith [kadd])) aub
                        simp at absurd
                    · have evalk := congr_arg (λ x ↦ Array.getD x b true) dropih
                      simp [Array.getD] at evalk
                      split at evalk
                      next cardlt =>
                        simp [cardlt, Array.getElem_append] at evalk
                        rw [← Nat.add_sub_assoc] at evalk
                        · simp [cardlt, ← Nat.not_le, blb] at evalk
                          exact evalk
                        · simp [-card_cons, card]
                          trans ((x :: y :: w).drop ((w.length + 1 + 1) / 2)).length
                          · apply List.countP_le_length
                          · simp
                      next _ cardge =>
                        rw [Nat.not_lt] at cardge
                        have absurd : w.length + 1 + 1 - (w.length + 1 + 1) / 2 < w.length + 1 + 1 - (w.length + 1 + 1) / 2 := Nat.lt_of_le_of_lt (Nat.le_trans cardge (by simp +arith [kadd])) bub
                        simp at absurd
                  have klttots : k < (totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.size + (totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.size := by
                    simp +arith [yl] at asize
                    simp +arith [asize, Vector.size]
                    rw [← Nat.add_sub_assoc]
                    · simpa
                    . omega
                  obtain ⟨i, j, ⟨kij, ijbounds⟩⟩ := bounded_sum kgecard klttots (by simp [-card_cons,card, Vector.size]; trans ((x :: y :: w).take ((w.length + 1 + 1) / 2)).length; apply List.countP_le_length; simp) (by simp [-card_cons,card, Vector.size]; trans ((x :: y :: w).drop ((w.length + 1 + 1) / 2)).length; apply List.countP_le_length; simp)
                  cases ijbounds with
                  | inl ilejlt =>
                    rw [Nat.le_iff_lt_or_eq] at ilejlt
                    cases ilejlt.left with
                    | inl ilt =>
                      apply kltcase kij.symm
                      · simp
                      · simp
                      · assumption
                      · exact ilejlt.right
                    | inr ieq =>
                      -- NOTE: Perhaps it makes sense to use (w.length ...) / 2 here directly instead of (totalizer ...).snd.fst.size?
                      have fit := sat #[(totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.get ⟨card (Multiset.ofList (List.drop ((w.length + 1 + 1) / 2) (x :: y :: w))) τ + j, ilejlt.right⟩, LitVar.mkNeg (mvar + (card (Multiset.ofList (List.drop ((w.length + 1 + 1) / 2) (x :: y :: w))) τ + j + (totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.fst.size))]
                      rw [Nat.add_comm] at kij
                      simp [← kij, ieq, Vector.size] at fit ⊢
                      rw [← Bool.not_eq_false, ← Decidable.imp_iff_not_or] at fit
                      apply fit
                      · right; right; right
                        use (List.finRange (w.length + 1 + 1 - (w.length + 1 + 1) / 2 + 1)).filterMap (λ i ↦ Fin.cases none (λ j ↦ some #[(totalizer (@Vector.mk _ ((w.length + 1 + 1) - (w.length + 1 + 1) / 2) ⟨List.drop ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp)) ((totalizer (@Vector.mk _ ((w.length + 1 + 1) / 2) ⟨List.take ((w.length + 1 + 1) / 2) (x :: y :: w)⟩ (by simp; omega)) (mvar + (m + 1 + 1))).snd.snd.getD (mvar + (m + 1 + 1)))).snd.fst.get j, LitVar.mkNeg (mvar + (j.val + (w.length + 1 + 1) / 2))]) i)
                        simp
                        use (⟨card (Multiset.ofList (List.drop ((w.length + 1 + 1) / 2) (x :: y :: w))) τ + j, by simp [Vector.size] at ilejlt; exact ilejlt.right⟩ : Fin _).succ
                        simp
                      · have evalk := congr_arg (λ z ↦ Array.getD z (card (Multiset.ofList (List.drop ((w.length + 1 + 1) / 2) (x :: y :: w))) τ + j) true) dropih
                        simp [-add_lt_add_iff_left, -Nat.add_lt_add_iff_left, Array.getD] at evalk
                        split at evalk
                        next cardlt =>
                          rw [← Nat.add_sub_assoc] at evalk
                          · simp [cardlt, ← Nat.not_le] at evalk
                            exact evalk
                          · simp [-card_cons, card]
                            trans ((x :: y :: w).drop ((w.length + 1 + 1) / 2)).length
                            · apply List.countP_le_length
                            · simp
                        next _ cardge =>
                          rw [Nat.not_lt] at cardge
                          have absurd : w.length + 1 + 1 - (w.length + 1 + 1) / 2 < w.length + 1 + 1 - (w.length + 1 + 1) / 2 := Nat.lt_of_le_of_lt (Nat.le_trans cardge (by simp +arith [kij])) ilejlt.right
                          simp at absurd
                  | inr iltjle =>
                    simp_rw [Nat.le_iff_lt_or_eq] at iltjle
                    cases iltjle.right with
                    | inl jlt =>
                      apply kltcase kij.symm
                      · simp
                      · simp
                      · exact iltjle.left
                      · assumption
                    | inr ieq =>
                      sorry

#eval Solver.Dimacs.printRichCnf IO.print ((((LawfulState.new ⟨5, by simp⟩ ⟨λ u : Fin 3 ↦ ⟨u.val.succ, by simp⟩, by intro a b; simp; rw [Subtype.mk_eq_mk]; simp [Fin.val_inj]⟩ (by intro v; simp; unfold LT.lt IVar.instLT; simp only [OfNat.ofNat]; trans (3 + 1); rw [Nat.add_one_lt_add_one_iff]; exact v.prop; simp) []).addClause #[Literal.pos 1, Literal.neg 2]).addClause #[Literal.neg 1, Literal.pos 2]).addClause #[Literal.neg 10, Literal.pos 19]).cnf
#eval (LawfulState.new ⟨5, by simp⟩ ⟨λ u : Fin 3 ↦ ⟨u.val.succ, by simp⟩, by intro a b; simp; rw [Subtype.mk_eq_mk]; simp [Fin.val_inj]⟩ (by intro v; simp; unfold LT.lt IVar.instLT; simp only [OfNat.ofNat]; trans (3 + 1); rw [Nat.add_one_lt_add_one_iff]; exact v.prop; simp) []).nextVar
#check (LawfulState.new ⟨5, by simp⟩ ⟨λ u : Fin 3 ↦ ⟨u.val.succ, by simp⟩, by intro a b; simp; rw [Subtype.mk_eq_mk]; simp [Fin.val_inj]⟩ (by intro v; simp; unfold LT.lt IVar.instLT; simp only [OfNat.ofNat]; trans (3 + 1); rw [Nat.add_one_lt_add_one_iff]; exact v.prop; simp) []).withTemps (none : Option (Fin 5 → String))

end Trestle.Encode.Cardinality
