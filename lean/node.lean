-- Polymorphism exercises 

-- Last entry in list
def List.findLast? (xs : List α) : Option α :=
match xs with
| List.nil => none
| List.cons y List.nil => some y
| List.cons _ ys => List.findLast? ys
#eval List.findLast? (α := Nat) [1,2,3,4,5]

-- First entry in list satisfying predicate
def List.findFirst? (xs : List α) (predicate : α → Bool) : Option α :=
match xs with
| [] => none
| y :: ys => if predicate y then some y else List.findFirst? ys predicate

#eval List.findFirst? [1, 2, 3, 4, 5] (· > 3)

-- Swap the two fields in a pair
def Prod.swap {α β : Type} (pair : α × β) : β × α := (pair.snd, pair.fst)
#eval Prod.swap (1,2)

-- Zip two lists into list of pairs
def zip : List α → List β → List (α × β)
| x :: xs, y :: ys => (x, y) :: zip xs ys
| _, _ => []
#eval zip [1,2,3] ["a", "b", "c", "d"]

def unzip : List (α × β) → List α × List β
| [] => ([], [])
| (x, y) :: xys =>
  let (xs, ys) := unzip xys
  (x :: xs, y :: ys)  

-- Take first n entries in the list
def take : List α → Nat → List α
| x :: xs, Nat.succ n => x :: take xs n
| _, _ => []
#eval take [1,2,3] 2

-- Function distributing products over sums
def distribute {α β γ : Type} (x : α × (β ⊕ γ)) : ((α × β) ⊕ (α × γ)) :=
match x.snd with
| Sum.inl y => Sum.inl (x.fst, y)
| Sum.inr y => Sum.inr (x.fst, y)

-- Function doubling a type
def double {α : Type} (x : Bool × α) : α ⊕ α :=
if x.fst then Sum.inl x.snd else Sum.inr x.snd

-- Running a program
def main2 : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "STATE YOUR NAME"  
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"

def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting

-- Interlude on proofs & propositions
theorem test1 : 2 + 3 = 5 := rfl
theorem test2 : 15 - 8 = 7 := rfl
theorem test3 : "Hello, ".append "world" = "Hello, world" := rfl

-- Functors: types exposing a map interface
#eval Functor.map List.reverse [[1,2,3], [4,5,6]]
#eval (· + 5) <$> [1, 2, 3]

-- Typeclass exercises

-- Write instance of HAppend for NonEmptyList

structure NonEmptyList (α : Type) : Type where
 head : α
 tail : List α
deriving Repr

def NonEmptyList.HAppend {α : Type} : List α → NonEmptyList α → NonEmptyList α
  | [], ys => ys
  | x :: xs, ys => {head := x, tail := xs ++ ys.head :: ys.tail}

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where 
  hAppend := NonEmptyList.HAppend

#eval [1,2,3] ++ ({head := 4, tail := [5,6,7]} : NonEmptyList Nat)

-- Write instance of Functor for BinTree

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α     
deriving Repr

def BinTree.Map {α β : Type} (f : α → β) : (BinTree α) → (BinTree β)
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l v r => BinTree.branch (BinTree.Map f l) (f v) (BinTree.Map f r)

instance : Functor BinTree where
  map f bt := BinTree.Map f bt

def tree :=
  (BinTree.branch
    BinTree.leaf
    2
    (BinTree.branch
      (BinTree.branch BinTree.leaf 3 BinTree.leaf)
      4
      (BinTree.branch BinTree.leaf 5 BinTree.leaf)
    )
  )
#eval (· * 2) <$> tree

-- Coercions

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
deriving Repr

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos)

-- Dependent coercions
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

#eval (([1,2,3] : List Nat) : NonEmptyList Nat)

-- Monoids
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (acc : M.Carrier) : List α → M.Carrier
    | [] => acc
    | y :: ys => go (M.op acc (f y)) ys
  go M.neutral xs

#eval foldMap stringMonoid (toString ·) [1,2,3]

--Applicative Functors
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()

--8.1 Exercises

inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (xs.zip ys)


-- Check zip gives right answer on mountain vecs
def OregonMountains :=
  (Vect.cons "Mount Hood" (
    Vect.cons "Mount Jefferson" (
      Vect.cons "South Sister" Vect.nil)))

def DenmarkMountains := 
  (Vect.cons "Møllehøj" (
    Vect.cons "Yding Skovhøj" (
      Vect.cons "Ejer Bavnehøj" Vect.nil)))

#eval OregonMountains.zip DenmarkMountains


-- Define Vect.map
def Vect.map : (α → β) → Vect α n → Vect β n
  | f, .nil => .nil
  | f, .cons x xs => .cons (f x) (map f xs)

#eval OregonMountains.map fun m => m.append  m

-- Define Vect.zipWith
def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
  | f, .nil, .nil => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

#eval OregonMountains.zipWith (fun om dm => om.append dm) DenmarkMountains

-- Define Vect.snoc
def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, v => .cons v .nil
  | .cons x xs, v => .cons x (snoc xs v)

#eval OregonMountains.snoc "North Sister"

-- Define Vect.reverse
def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => (reverse xs).snoc x

#eval OregonMountains.reverse

-- Define Vect.drop
def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | (j + 1), .cons _ xs => Vect.drop j xs

#eval DenmarkMountains.drop 2

-- Define Vect.take
def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | (j + 1), .cons x xs => .cons x (take j xs)

#eval OregonMountains.take 2