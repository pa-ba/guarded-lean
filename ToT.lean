-- This module serves as the root of the `ToT` library.
-- Import modules here that should be built as part of the library.
import Lean

structure ToTType where
  F : Nat → Type
  restr : (n : Nat) → F (n + 1) → F n

def ToTType.cast {A : ToTType} (p : n = k) : A.F n → A.F k := (p ▸ ·)

@[simp]
theorem ToTType.cast_refl_id {A : ToTType} {p : n = n} {x : A.F n} : A.cast p x = x := by
  cases p
  rfl

@[simp]
theorem ToTType.cast_cast_trans {A : ToTType} {p : n = k} {q : k = j} {x : A.F n} : A.cast q (A.cast p x) = A.cast (p.trans q) x := by
  cases p
  rfl

theorem Subtype.valEq : x = w -> Subtype.mk x y = Subtype.mk w z :=
  by
   intro h
   cases h
   rfl

def ToTType.restrmaphelp (n : Nat) : (k : Nat) → F A (n + k) → F A n
  | 0, a => a
  | h+1 , a =>
    let p : (n + (h + 1)) = (n + 1 + h) := by omega
    A.restr n (restrmaphelp (n+1) h (A.cast p a))
--  | h+1 , a => restrmaphelp n h (A.restr (n+h) a)

def restrmaphelpzero
    (n k : Nat)
    (p : k = 0) (q : n + k = n)
    (x : ToTType.F A (n+k))
    : ToTType.restrmaphelp n k x = A.cast q x := by
  cases p
  simp [ToTType.restrmaphelp]

def restrmaphelpsucc (n k : Nat)
    (p : k = k'+ 1)
    (q : n + k = n + 1 + k')
    (x : ToTType.F A (n+k))
    : ToTType.restrmaphelp n k x = A.restr n (ToTType.restrmaphelp (n+1) k' (A.cast q x)) := by
  cases p
  simp [ToTType.restrmaphelp]

def LThelp (n m : Nat) (h : m ≤ n) : {k : Nat // m+k = n} where
  val := n-m
  property := by
--     omega
     exact Nat.add_sub_of_le h
     -- Found using apply?
     -- by omega tactic

def LThelpZero (m n : Nat) (p : m+1=n) (q : m+1 ≤ n) : (LThelp n (m+1) q).val = 0
  := by
      have : n-(m+1) = 0 := by omega
      unfold LThelp
      simp[this]

@[simp]
def LThelpVal (m n : Nat) (p : m ≤ n) : (LThelp n m p).val = n - m
  := by
      unfold LThelp
      simp

def ToTType.testr (n m : Nat) (p : n=m) (a : F A n) : F A m
  := p ▸ a
  -- let q : F A n = F A m := by rw[p];
  -- cast q a

def ToTType.restrmap (h : m ≤ n) (a : F A n) : F A m
  := let ⟨ n_minus_m, p⟩ := LThelp n m h;
     let q : n = (m + n_minus_m) := by rw[p];
     restrmaphelp m n_minus_m (A.cast q a)


set_option pp.proofs.withType true

def ToTType.restrmapEq
    (p : m+1 ≤ n)
    (q : m ≤ n)
    (a : F A n)
    : A.restr m (restrmap p a) = restrmap q a := by
  let d := LThelp n (m+1) p
  let ⟨ k, klt⟩ := d
  induction k with
  | zero =>
    simp only [restrmap]
    rw [restrmaphelpzero] <;> try (simp_arith; omega)
    rw [restrmaphelpsucc (k':=0)] <;> try (simp_arith; omega)
    rw [restrmaphelpzero] <;> try rfl
    simp
  | succ k' =>
    simp only [restrmap]
    -- conv => lhs ; unfold restrmaphelp
    have : (LThelp n (m + 1) p).val = k'+ 1 := by
      simp; omega
    apply Eq.symm
    have := restrmaphelpsucc (A := A) (n := m) (k := (LThelp n m q).val) (k' := (LThelp n (m + 1) p).val) (p := by simp; omega) (q := by simp; omega) <| by
      simp
      apply cast ?prf
      . exact a
      . omega
    simp at this
    apply this

def ToTType.restrmaphelpEqInnerZero
  (m n : Nat)
  (A : ToTType)
  (p : m ≤ n + 1)
  (q : m ≤ n)
  (a : A.F (n + 1))
  (klt : m + 0 = n)
  : restrmap p a = restrmap q (A.restr n a) := by
    simp at klt
    cases klt
    simp[restrmap]
    have := restrmaphelpzero (A := A) m (LThelp m m q).val ?e (by simp)
    rw[this]
    simp
    have := restrmaphelpsucc (k':=0) m (A := A) 1 rfl rfl a
    rw[restrmaphelpsucc (k':=0)] <;> try (simp_arith; omega)
    rw[restrmaphelpzero ] <;> try (simp_arith; omega)
    case q => rfl
    all_goals (try simp[LThelp])
    case q => omega
    simp

def ToTType.restrmapEqInner
    (p : m ≤ n+1)
    (q : m ≤ n)
    (a : F A (n+1))
    : restrmap p a = restrmap q (A.restr n a) := by
      let ⟨ k, klt⟩ := LThelp n m q
      induction k with
      | zero =>
        simp[restrmap]
        simp at klt
        cases klt
        simp[LThelp]
        have : m-m = 0 := by simp_arith
        apply restrmaphelpEqInnerZero <;> omega
      | succ k' =>
        sorry


def ToTHom (A B : ToTType) : Type
    := {f : (n : Nat) → A.F (n) → B.F (n) // (∀n x, B.restr n (f (n+1) x) = f n (A.restr n x))}

instance : Coe Type ToTType where
  coe T := { F := fun _ => T, restr := fun _ => id}

infixr:60 " ⤳ " => ToTHom

def ToTType.delta {A B : Type} (f : A → B) : A ⤳ B where
  val := fun _ => f
  property := by
      intro n
      intro x
      rfl

def ToTType.const {A : ToTType} {B : Type} (b : B) : A ⤳ B where
  val := fun n _ => b
  property := by
    intro n
    intro x
    rfl

def ToTType.id : A ⤳ A where
  val :=  fun _ x => x
  property :=  by
    intro n
    intro y
    rfl

def ToTType.comp (f : A ⤳ B) (g : B ⤳ C) : A ⤳ C where
  val := fun n => g.val n ∘ f.val n
  property := by
    intro n x
    let ⟨ fval, fprop⟩ := f
    let ⟨ gval, gprop⟩ := g
    simp
    rw [← fprop, ← gprop]

-- Associativity, lid and rid, later, fixpoints, streams, guarded recursive types

def ToTType.Later (A : ToTType) : ToTType where
  F := fun
        | 0 => Unit
        | n+1 => A.F n
  restr := fun
        | 0, _ => ()
        | n+1, x => A.restr n x

notation:70 "▷" T => ToTType.Later T

def ToTType.Earlier (A : ToTType) : ToTType where
  F := fun n => A.F (n+1)
  restr := fun n => A.restr (n+1)

notation:70 "◁" T => ToTType.Earlier T

def ToTType.delayF (f : (◁ A) ⤳ B) : (n : Nat) → A.F n → (▷B).F n
 | 0 , _ => ()
 | n+1 , a => f.val n a

def ToTType.delay (f : (◁ A) ⤳ B) : A ⤳ ▷B where
  val := delayF f
  property := by
      intro n
      cases n with
      | zero =>
        simp [delayF]
        intro x
        cases (▷B).restr 0 (f.val 0 x)
        rfl
      | succ n =>
        simp [delayF]
        exact f.property n

def ToTType.adv (f : A ⤳ ▷B) : (◁A) ⤳ B where
  val := fun n => f.val (n+1)
  property := fun n => f.property (n+1)

def ToTType.next : A ⤳ ▷A where
  val
   | 0, _ => ()
   | n+1, a => A.restr n a
  property := by
               intro n x
               simp
               induction n with
               | zero => simp[Later]
               | succ m _ => simp[Later]

def ToTType.prev : (◁Γ) ⤳ Γ := adv (next)

def ToTType.Prod (A B : ToTType) : ToTType where
  F := fun n => (A.F n)× (B.F n)
  restr := fun n x => (A.restr n (Prod.fst x), B.restr n (Prod.snd x))

def ToTType.fst : (ToTType.Prod A B) ⤳ A where
  val := fun n => Prod.fst
  property := by
               intro n
               intro x
               rfl


def ToTType.snd : (ToTType.Prod A B) ⤳ B where
  val := fun n => Prod.snd
  property := by
               intro n
               intro x
               rfl

--def ToTType.pair (A B C : ToTType) (f : C ⤳ A) (g : C ⤳ B) : (C ⤳ ToTType.Prod A B) where
def ToTType.pair (f : C ⤳ A) (g : C ⤳ B) : (C ⤳ ToTType.Prod A B) where
  val := fun n c => (f.val n c, g.val n c)
  property := by
               intro n
               intro x
               simp [ToTType.restr,Prod]
               constructor
               case left => exact f.property n x
               case right => exact g.property n x

def ToTType.unitFinal : A ⤳ Unit where
  val := fun _ _ => ()
  property := by
               intro n _
               simp


def ToTType.cutF (A : ToTType) (n : Nat) : Nat → Type :=
  fun m => PProd (m ≤ n) (A.F m)

def cutincl {A : ToTType} (a : A.F n) : (ToTType.cutF A n n) :=
 let p : (n ≤ n) := by omega
 ⟨p, a⟩

def ToTType.cut (A : ToTType) (n : Nat) : ToTType where
  F := cutF A n
  restr := fun m ⟨h, y⟩ =>
   ⟨by exact Nat.le_of_succ_le h, A.restr m y⟩

def ToTType.cutRestr {A : ToTType} {n : Nat} : (cut A n)⤳(cut A (n+1)) where
  val := fun m ⟨h, y⟩ =>
    ⟨by omega, y⟩
  property := by
    intro p
    intro x
    simp
    split
    simp[cut]

def ToTType.Fun (A B : ToTType) : ToTType where
  F := fun n => cut A n ⤳ B
  restr := fun _ h => comp cutRestr h

def ToTType.ev : Prod (Fun A B) A ⤳ B where
  val := fun n => fun fa =>
    let f := (Prod.fst fa).val n
    let a := (Prod.snd fa)
    let xa := cutincl a
    f xa
  property := by
    intro n
    intro fa
    dsimp
--    have xfun := x.fst
--    have xa := cutincl fa.snd
--    have q : x = (xfun,xa) := by sorry
    simp[Prod,Fun,comp,cutRestr,cutincl]
--    let xsnd : (cut A (n + 1)).F (n + 1) := cutincl x.snd
    --let z :
--    let a := (Prod.snd fa)
    let r := fa.fst.property n (cutincl fa.snd) --(by sorry, xa)
    --let p : xa = ⟨_, x.fst⟩ := by omega
--    exact r
    --apply?
    simp[cutincl] at r
    rw[r]
    simp[cut]

def ToTType.lamF (f : Prod A B ⤳ C) (n : Nat) (a : F A n) : cut B n ⤳ C where
  val := fun m b =>
    let p : m ≤ n := b.fst
    let bval : F B m := b.snd
    let a_restr : F A m := restrmap p a
    f.val m (a_restr, bval)
  property := by
      intro m b
      simp
      let h : (m+1 ≤ n) := b.fst
      let y := f.property m (restrmap h a, b.snd)
      rw[y]
      apply congrArg
      simp [Prod]
      constructor
      . apply restrmapEq
      . simp [cut]
        cases b
        simp


def ToTType.lam (f : Prod A B ⤳ C) : A ⤳ Fun B C where
 val := lamF f
 property := by
   intro n x
   let ⟨fval, fprop⟩ := f
   simp [lamF, Fun, comp]
   apply Subtype.valEq
   funext m b
   simp[Prod] at fprop
   simp[· ∘ ·]
   apply congrArg
   ext
   . simp
     sorry
   . simp
     simp[cutRestr]
     cases b
     simp


def ToTType.deltaFun {A B : Type} (f : A → B) : Γ ⤳ Fun A B :=
  lam (comp snd (delta f))

def ToTType.funcomp : Prod (Fun A B) (Fun B C) ⤳ Fun A C
  := let firststep : Prod (Prod (Fun A B) (Fun B C)) A ⤳ B
       := comp (pair (comp fst fst) snd) ev;
     let resultcurr : Prod (Prod (Fun A B) (Fun B C)) A ⤳ C
       := comp (pair (comp fst snd) firststep) ev;
     lam resultcurr


def ToTType.appfun : Prod (▷(Fun A B)) (▷A) ⤳ ▷B
 := let f : (◁(Prod (▷(Fun A B)) (▷A))) ⤳ Fun A B
          := adv fst;
    let x : (◁(Prod (▷(Fun A B)) (▷A))) ⤳ A
          := adv snd;
    let fx : (◁(Prod (▷(Fun A B)) (▷A))) ⤳ B := (comp (pair f x) ev);
    ToTType.delay fx


def fixpval {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A): (n : Nat) →  Γ.F n → A.F n
  | 0, γ => f.val 0 (γ, ())
  | n+1, γ => f.val (n+1) (γ, fixpval f n (Γ.restr n γ))

def fixprop {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A) : (n : Nat) →  (γ : Γ.F (n+1)) → fixpval f (n+1) γ = f.val (n+1) (γ, fixpval f n (Γ.restr n γ))
  | 0, γ => by
             simp[fixpval]
  | n+1, γ => by
               simp[fixpval]

def fixp {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A) : Γ ⤳ A where
  val := fixpval f
  property := by
    intro n γ
    induction n with
    | zero => simp[fixpval]
              apply f.property
    | succ m p => simp[fixpval,f.property,fixprop,ToTType.Prod]
                  simp[ToTType.Later]
                  --let q := p (Γ.restr (m + 1) γ)
                  exact
                    congrArg (f.val (Nat.succ m))
                      (congrArg (Prod.mk (Γ.restr (Nat.succ m) γ)) (p (Γ.restr (m + 1) γ)))

def fixpoint (A : ToTType) (f : (▷A) ⤳ A) : (Unit ⤳ A)
  := let g : ToTType.Prod Unit (▷A) ⤳ A := ToTType.comp ToTType.snd f;
     fixp g

-- Show fixpoint is fixed point

def ToTType.StrF (A : Type) : Nat → Type
  | 0 => A × Unit
  | n + 1 => A × StrF A n

def ToTType.StrR (A : Type) : (n : Nat) → StrF A (n+1) → StrF A n
   | 0, (a, _) => (a, ())
   | n+1, (a, as) => (a, StrR A n as)

def ToTType.Str (A : Type) : ToTType where
  F := ToTType.StrF A
  restr := StrR A

--def ToTType.Str.tailmap (A : Type) (xs : ToTType.Str A) : (n : Nat) →

def ToTType.StrUnfold (A : Type) (n : Nat) : (ToTType.Str A).F n = (A × (▷(ToTType.Str A)).F n)
 := by
      simp[Str,Later]
      cases n
      simp
      rfl
      simp[StrF]

def ToTType.Str.tail {A : Type} : ToTType.Str A ⤳ ▷(ToTType.Str A) where
     val
      | 0, a => a.snd
      | n+1, a => a.snd
     property := by
                  intro n x
                  simp[Later]
                  cases n
                  simp
                  constructor


def ToTType.Str.headmap {A : Type} : (n : Nat) →  (as : (Str A).F n) →  A
  := fun n a => ((StrUnfold A n) ▸ a).fst

def ToTType.Str.head {A : Type} : ToTType.Str A ⤳ A where
     val := headmap
     property := by
                  intro n
                  intro x
                  simp[headmap, Str, StrR]
                  induction n with
                  | zero => simp[StrR]
                  | succ m _ => simp[Later,StrR]

def ToTType.Str.consmap {Γ : ToTType} {B : Type} (g : Γ ⤳ B) (f : Γ ⤳ ▷(ToTType.Str B)) (n : Nat) : Γ.F n → (ToTType.Str B).F n
  := fun γ => StrUnfold B n ▸ (g.val n γ, f.val n γ)

def ToTType.Str.cons {Γ : ToTType} {B : Type} (g : Γ ⤳ B) (f : Γ ⤳ ▷(ToTType.Str B)) : Γ ⤳ (ToTType.Str B) where
  val := consmap g f
  property := by
     intro n x
     simp[consmap,Str]
     induction n with
     | zero => simp[StrR]
               apply congr
               apply congr
               rfl
               exact g.property 0 x
               constructor
     | succ m _ => simp[StrR]
                   apply congr
                   apply congr
                   rfl
                   exact g.property (m+1) x
                   exact f.property (m+1) x

def zeros : Unit ⤳ ToTType.Str Nat := fixpoint (ToTType.Str Nat) (ToTType.Str.cons (ToTType.const 0) (ToTType.id))

--- zeros : ToTType.Str Nat := fix x. 0 :: x
--- cons (a : A) (xs : Str A) := fold (a, xs)

declare_syntax_cat ToTExpr
syntax "[" term "]" : ToTExpr
syntax "fix" "(" ident ":" term ")" "=>" ToTExpr : ToTExpr
syntax "fun" "(" ident ":" term ")" "=>" ToTExpr : ToTExpr
syntax ToTExpr ToTExpr : ToTExpr
syntax ident : ToTExpr
syntax ToTExpr "::" ToTExpr : ToTExpr
syntax "adv(" ToTExpr ")" : ToTExpr
syntax "delay(" ToTExpr ")" : ToTExpr
syntax "(" ToTExpr ")" : ToTExpr
syntax "box(" ToTExpr ")" : term

structure Ctxt where
  here : Nat := 0
  previous : List Nat := []

def Ctxt.bindvar (c : Ctxt) : Ctxt where
  here := c.here +1
  previous := c.previous

def Ctxt.tick (c : Ctxt) : Ctxt where
  here := 0
  previous := c.here :: c.previous

def Ctxt.untick (c : Ctxt) : Option Ctxt :=
  match c.previous with
  | [] => none
  | x :: xs => some {here := x, previous := xs}

def Ctxt.size (c : Ctxt) : Nat := c.previous.foldl (· + ·) c.here

open Lean Elab Term
def lookup (vars : Ctxt) (index : Nat) : TermElabM (TSyntax `term) :=
  match vars, index with
  | ⟨0,[]⟩ , _ => throwError "No variables in scope"
  | ⟨0, x :: xs⟩ , i => do
    let inner ← lookup ⟨x, xs⟩ i
    `(ToTType.comp ToTType.prev $inner)
  | ⟨k+1, xs⟩ , 0 => `(ToTType.snd)
  | ⟨k+1, xs⟩ , n+1 => do
    let inner ← lookup ⟨k, xs⟩ n
    `(ToTType.comp ToTType.fst $inner)

partial def elabToTExpr (vars : Ctxt) (levels : NameMap Nat) (stx : TSyntax `ToTExpr ) : TermElabM (TSyntax `term) :=
  -- dbg_trace stx
  match stx with
  | `(ToTExpr|[$t]) => `(ToTType.const $t)
  | `(ToTExpr|fix ($x : $A) => $body) => do
    let bodyExpr <- elabToTExpr (vars.bindvar) (levels.insert x.getId vars.size) body
    `(fixp (A := $A) $bodyExpr)
  | `(ToTExpr|fun ($x : $A) => $body) => do
    let bodyExpr <- elabToTExpr (vars.bindvar) (levels.insert x.getId vars.size) body
    `(ToTType.lam (B := $A) $bodyExpr)
  | `(ToTExpr|$e1 $e2) => do
    let f <- elabToTExpr vars levels e1
    let a <- elabToTExpr vars levels e2
    `(ToTType.comp (ToTType.pair $f $a) ToTType.ev)
  | `(ToTExpr|$x:ident) => do
    if let some n := levels.find? x.getId then lookup vars (vars.size-n-1)
     else throwErrorAt x "Not a ToT variable"
  | `(ToTExpr|$h :: $t) => do
    let hd <- elabToTExpr vars levels h
    let tl <- elabToTExpr vars levels t
    `(ToTType.Str.cons $hd $tl)
  | `(ToTExpr|adv($d)) => do
    if let some vars' := vars.untick then
      let e <- elabToTExpr vars' levels d -- Todo: Add projection: iterate fst vars.here times
      `(ToTType.adv $e)
    else throwErrorAt stx "No ticks in the context"
  | `(ToTExpr|delay($d)) => do
    let e <- elabToTExpr vars.tick levels d
    `(ToTType.delay $e)
  | `( ToTExpr|($t)) => elabToTExpr vars levels t
  | _ => throwErrorAt stx "Did not understand"

elab_rules : term
  | `( box($t) ) => do
    let f <- elabToTExpr {} {} t
    dbg_trace Syntax.prettyPrint f
    elabTerm f none

#eval (box([4+3]) : Unit ⤳ Nat).val 0 ()

def pretty_zeros : Unit ⤳ ToTType.Str Nat := box(fix (tl : _) => [0]::tl)
def ugly_zeros : Unit ⤳ ToTType.Str Nat := box(fix (tl : _) => [0]::delay(adv(tl)))
def blah : Unit ⤳ Nat := box((fun (x : Nat) => x) [12])
def blahblah : Unit ⤳ Nat := box(((fun (x : Nat) => (fun (y: Nat) => y)) [12]) [14])
def pretty_from : Unit ⤳ (ToTType.Str Nat) :=
--   box(fun (n : _) => fix (f : _) => n ::(f ([ToTType.deltaFun (Nat.succ)] n)))
   box((fix (f : ToTType.Fun Nat (ToTType.Str Nat)) => fun (n : _) => n ::delay(adv(f) n))[5])


#eval blah.val 0 ()
#eval blahblah.val 0 ()
--#eval ToTType.Str.take pretty_zeros 8

def Box (A : ToTType) : Type := Unit ⤳ A

abbrev Scream (A : Type) := Box (ToTType.Str A)

def force {A : ToTType} (b : Box (▷A)) : Box A where
  val := fun n => b.val (n+1)
  property := by
               intro n x
               simp
               exact b.property (n+1) x

def ToTType.Str.cihead {A : Type} (s : Scream A) : A := (s.val 0 ()).fst

def ToTType.Str.citail {A : Type} (s : Scream A) : Scream A := force (ToTType.comp s ToTType.Str.tail)

def ToTType.Str.take (s : Scream A) : Nat → List A
  | 0 => []
  | n+1 => cihead s :: Str.take (citail s) n

def ToTType.Str.map {A B : Type} (f : A ⤳ B) : (Str A) ⤳ (Str B) :=
  let appf : (Str A) ⤳ B
    := comp head f;
  let hdout : (ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A)) ⤳ B
    := comp snd appf;
  let dgrass : (ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A)) ⤳ ▷(Fun (Str A) (Str B))
    := ToTType.fst;
  let grass : (◁(ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A))) ⤳ (Fun (Str A) (Str B))
    := adv (dgrass); -- GR assumption, grass
  let tl : ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A) ⤳ ▷(Str A)
    := comp snd tail;
  let delaytl : (◁(ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A))) ⤳ Str A
    := adv (tl);
  let tlout : ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A) ⤳ ▷(Str B)
    := delay (comp (pair grass delaytl) ev)
  let fpterm : (▷(Fun (Str A) (Str B))) ⤳ Fun (Str A) (Str B)
    := lam (cons hdout tlout);
  let resultcurr : Unit ⤳ Fun (Str A) (Str B)
    := fixpoint (Fun (Str A) (Str B)) fpterm;
  let resultuncurr : Prod Unit (Str A) ⤳ Str B
    := comp (pair (comp fst resultcurr) snd) ev;
  comp (pair unitFinal ToTType.id) resultuncurr

def ToTType.Str.from : Nat ⤳ (Str Nat) :=
   let hdout : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Nat
     := snd
   let succsnd : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Nat
     := comp snd (delta (fun n => n+1))
   let tlout : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ ▷ (Str Nat)
     := comp (pair fst (comp succsnd next)) appfun
   let fpfuncurr : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Str Nat
     := cons hdout tlout
   let fpfun : (▷(Fun Nat (Str Nat))) ⤳ Fun Nat (Str Nat)
     := lam fpfuncurr
   let almostresult : Nat ⤳ Fun Nat (Str Nat)
     := fixp (comp snd fpfun)
   comp (pair almostresult id) ev

def ToTType.Str.natseq : Box (Str Nat) := comp (delta (fun _ => 0)) Str.from

#eval ToTType.Str.take (ToTType.Str.natseq) 8

#eval ToTType.Str.take pretty_from 8

--#eval ToTType.Str.take zeros 8
#eval ToTType.Str.take pretty_zeros 8

--#check Nat ⤳ Nat
