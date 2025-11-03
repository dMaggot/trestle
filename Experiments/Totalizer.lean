import Trestle.Encode.Cardinality.Defs
import Trestle.Solver.Dimacs

namespace Trestle.Encode.Cardinality

open EncCNF Model PropFun

-- NOTE: Maybe return a Vector of ν so that one can use Literal.{pos,neg} directly.
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
      -- FIXME These folds/mapFinIdxs should be restructured to 1) either use concat or flatten but not both and 2) merge consecutive mapFnIdxs
  ⟨ltot.fst ++ rtot.fst ++ ⟨(List.foldl List.concat (List.mapFinIdx ltot.snd.fst.toList (λ i _ ilt ↦ #[LitVar.negate (ltot.snd.fst.toList.get ⟨i, ilt⟩), Literal.pos (newVars.get ⟨i, by next klen _ => simp [← Array.length_toList] at klen; simp [newVars, h, Vector.size, ← klen]; simp [ltot] at ilt; trans (t.length + 1 + 1) / 2; assumption; omega⟩)])) []) ++ List.flatten (List.mapFinIdx ltot.snd.fst.toList (λ i _ ilt ↦ (List.mapFinIdx rtot.snd.fst.toList (λ j _ jlt ↦ #[LitVar.negate (rtot.snd.fst.toList.get ⟨j, jlt⟩), Literal.pos (newVars.get ⟨j, by next klen _ _ => simp [← Array.length_toList] at klen; simp [newVars, h, Vector.size, ← klen]; simp [rtot] at jlt; trans t.length + 1 + 1 - (t.length + 1 + 1) / 2; assumption; simp⟩)])) ++ (List.mapFinIdx rtot.snd.fst.toList (λ j _ jlt ↦ #[LitVar.negate (ltot.snd.fst.toList.get ⟨i, ilt⟩), LitVar.negate (rtot.snd.fst.toList.get ⟨j, jlt⟩), Literal.pos (newVars.get ⟨(i + j).succ, by next klen _ _ => simp [newVars, h, Vector.size, ← klen]; simp [ltot] at ilt; simp [rtot] at jlt; rw [Nat.sub_add_comm, Nat.lt_iff_le_pred] at jlt; simp at jlt; have ijlt := Nat.add_lt_add_of_lt_of_le ilt jlt; rw [← Nat.add_sub_assoc] at ijlt; simp at ijlt; exact ijlt; omega; omega; omega⟩)]))))⟩ ++ ⟨List.foldl List.concat (List.mapFinIdx ltot.snd.fst.toList (λ i _ ilt ↦ #[Literal.neg (newVars.get ⟨i + rtot.snd.fst.size, by next klen _ => simp +arith [newVars, h, Vector.size, ← klen]; rw [← Nat.add_sub_assoc, Nat.sub_le_iff_le_add]; simp +arith [ltot] at ilt ⊢; assumption; omega⟩), ltot.snd.fst.toList.get ⟨i, ilt⟩])) [] ++ List.flatten (List.mapFinIdx ltot.snd.fst.toList (λ i _ ilt ↦ (List.mapFinIdx rtot.snd.fst.toList (λ j _ jlt ↦ #[Literal.neg (newVars.get ⟨j + ltot.snd.fst.size, by next klen _ _ => simp +arith [newVars, h, Vector.size, ← klen]; simp +arith [ltot, Nat.lt_sub_iff_add_lt] at jlt; assumption⟩), rtot.snd.fst.toList.get ⟨j, jlt⟩])) ++ (List.mapFinIdx rtot.snd.fst.toList (λ j _ jlt ↦ #[Literal.neg (newVars.get ⟨i + j, by next klen _ _ => simp [newVars, h, Vector.size, ← klen]; simp +arith [ltot] at ilt; simp +arith [rtot] at jlt; have ijlt := Nat.add_lt_add_of_le_of_lt ilt jlt; rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left] at ijlt; trans t.length + 1; assumption; simp; omega⟩), ltot.snd.fst.toList.get ⟨i, ilt⟩, rtot.snd.fst.toList.get ⟨j, jlt⟩]))))⟩, ⟨@Vector.mk _ c.size ⟨newVars⟩ (by simp [newVars, -List.pure_def, -List.bind_eq_flatMap, List.size_toArray]), Option.getD rtot.snd.snd (nextVar + c.size)⟩⟩
termination_by c.size
decreasing_by
next klen =>
  simp [h, Vector.size, ← klen]
  omega
next klen =>
  simp [h, Vector.size, ← klen]
next klen =>
  simp [h, Vector.size, ← klen]
  omega
next klen =>
  simp [h, Vector.size, ← klen]
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
next klen =>
  simp [h, Vector.size, ← klen]
  omega
next klen =>
  simp [h, Vector.size, ← klen]
  omega
next klen =>
  simp [Vector.size, ← klen]
  omega
next klen =>
  simp [Vector.size, ← klen]
  omega
next klen =>
  simp [Vector.size, ← klen]
  omega
next klen =>
  simp [Vector.size, ← klen]
  omega
next klen =>
  simp [Vector.size, ← klen]
  omega
next klen =>
  simp [Vector.size, ← klen]
  omega
next klen =>
  simp [Vector.size, ← klen]
next klen =>
  simp [Vector.size, ← klen]
next klen =>
  simp [Vector.size, ← klen]
next klen =>
  simp [Vector.size, ← klen]

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
  -- NOTE: How come I have to do this in 2 steps?
  unfold totalizer at sat
  simp at sat
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
      have m1 := sat #[LitVar.mkNeg (m + 1), b]
      simp [atrue, bfalse] at m1
      tauto
  next afalse =>
    simp [SemanticEntails.entails, satisfies] at afalse
    have m1 := sat #[LitVar.mkNeg (m + 1), a]
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
      have m0 := sat #[LitVar.mkNeg (m + 0), a, b]
      simp [afalse, bfalse] at m0
      tauto

#eval Solver.Dimacs.printRichCnf IO.print ((((LawfulState.new ⟨5, by simp⟩ ⟨λ u : Fin 3 ↦ ⟨u.val.succ, by simp⟩, by intro a b; simp; rw [Subtype.mk_eq_mk]; simp [Fin.val_inj]⟩ (by intro v; simp; unfold LT.lt IVar.instLT; simp only [OfNat.ofNat]; trans (3 + 1); rw [Nat.add_one_lt_add_one_iff]; exact v.prop; simp) []).addClause #[Literal.pos 1, Literal.neg 2]).addClause #[Literal.neg 1, Literal.pos 2]).addClause #[Literal.neg 10, Literal.pos 19]).cnf
#eval (LawfulState.new ⟨5, by simp⟩ ⟨λ u : Fin 3 ↦ ⟨u.val.succ, by simp⟩, by intro a b; simp; rw [Subtype.mk_eq_mk]; simp [Fin.val_inj]⟩ (by intro v; simp; unfold LT.lt IVar.instLT; simp only [OfNat.ofNat]; trans (3 + 1); rw [Nat.add_one_lt_add_one_iff]; exact v.prop; simp) []).nextVar

end Trestle.Encode.Cardinality
