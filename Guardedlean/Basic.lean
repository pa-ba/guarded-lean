import Std


axiom Later : (α : Type) → Type

axiom delay : {α : Type} → α → Later α

axiom app : {α β : Type} → Later (β → α) → Later β → Later α

infixl:65   " <*> " => app

axiom Fix : (f : Type → Type) → Type

axiom Fix_beta : (f : Type → Type) → Fix f = f (Later (Fix f))

axiom fix : {α : Type} → (f : Later α → α) → α

def Str (α : Type) : Type := Fix (fun T => α × T)

def Str.unfold (s : Str α) : α × Later (Str α) := Fix_beta (fun T => α × T) ▸ s


def Str.head (s : Str α) : α := s.unfold.fst
def Str.tail (s : Str α) : Later (Str α) := s.unfold.snd

def Str.cons {α : Type} (x : α ) (xs : Later (Str α )) : Str α :=
  let xs' : Fix (fun T => α × T) :=  (Fix_beta (fun T => α × T)) ▸ (x , xs)
  xs'

infixr:65   " :: " => Str.cons

axiom fix_beta : {α : Type} → {f : Later α → α} → fix f = f (delay (fix f ))

noncomputable def zeros : Str Nat := fix (fun x => 0 :: x)

theorem zeros_unfold : zeros = .cons 0 (delay zeros) := by
  simp [zeros]
  conv => lhs ; rw [fix_beta]

noncomputable def map {α β : Type} (f : α → β) : Str α → Str β :=
  fix fun r => fun xs => f xs.head :: (r <*> xs.tail)
