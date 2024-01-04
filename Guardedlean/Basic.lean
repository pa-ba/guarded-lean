import Std

universe u

axiom Later : (α : Type u) → Type u

axiom delay : {α : Type u} → α → Later α

axiom app : {α β : Type u} → Later (β → α) → Later β → Later α

axiom Fix : (f : Type u → Type u) → Type u

axiom Fix_beta : (f : Type u → Type u) → Fix f = f (Later (Fix f))


-- inductive Str (α : Type u) : Type u where
--   | cons : (head : α) → (tail : Later (Str α)) → Str α

axiom fix : {α : Type u} → (f : Later α → α) → α

abbrev Str (α : Type u) : Type u := Fix (fun T => α × T)

def Str.unfold (s : Str α) : α × Later (Str α) := Fix_beta (fun T => α × T) ▸ s

def Str.head (s : Str α) : α := s.unfold.fst
def Str.tail (s : Str α) : Later (Str α) := s.unfold.snd

def Str.cons {α : Type u} (x : α ) (xs : Later (Str α )) : Str α :=
  let xs' : Fix.{u} (fun T => α × T) :=  (Fix_beta.{u} (fun T => α × T)) ▸ (x , xs)
  xs'

axiom fix_beta : {α : Type u} → {f : Later α → α} → fix f = f (delay (fix f ))

-- --partial def fix [Inhabited α] (f : Later α → α) : α := f (.delay (fun _ => fix f))

noncomputable def zeros : Str Nat := fix (fun x => .cons 0 x)

theorem zeros_unfold : zeros = .cons 0 (delay zeros) := by
  simp [zeros]
  conv => lhs ; rw [fix_beta]

def map {α β : Type u} (f : α → β) : Str α → Str β :=
  fix.{u} fun r => fun xs =>
    let x' := Str.head.{u} xs
    .cons _ _ --(app.{u} xs.tail _)
