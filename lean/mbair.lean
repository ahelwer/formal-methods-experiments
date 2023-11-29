inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def example_tree :=
  BinTree.branch
    (BinTree.branch
      (BinTree.branch BinTree.leaf 6 BinTree.leaf)
      5
      (BinTree.branch BinTree.leaf 4 BinTree.leaf)
    )
    3
    (BinTree.branch
      (BinTree.branch BinTree.leaf 2 BinTree.leaf)
      1
      (BinTree.branch BinTree.leaf 0 BinTree.leaf)
    )

def BinTree.enumerate (t : BinTree α) : BinTree (Nat × α) :=
  let rec rank_from : Nat → BinTree α → Nat × BinTree (Nat × α)
    | n, BinTree.leaf => (n, BinTree.leaf)
    | n, BinTree.branch l x r =>
      let (n, l) := rank_from n l
      let (n, x) := (n + 1, (n, x))
      let (n, r) := rank_from n r
      (n, BinTree.branch l x r)
  let (_, t') := rank_from 0 t
  t'

#eval example_tree.enumerate

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def BinTree.enumerateState (t : BinTree α) : BinTree (Nat × α) :=
  let rec enumerate_from : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => fun s => (s, BinTree.leaf)
    | BinTree.branch l x r => fun s =>
      let (s, l) := (enumerate_from l) s
      let (s, x) := (fun s => (s + 1, (s, x))) s
      let (s, r) := (enumerate_from r) s
      (s, BinTree.branch l x r)
    let (_, t) := enumerate_from t 0
    t

#eval example_tree.enumerateState

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
 fun s =>
  let (s', v) := first s
  next v s'

infixl:55 " ~~> " => andThen

def BinTree.enumerateAndThen (t : BinTree α) : BinTree (Nat × α) :=
  let rec enumerate_from : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => fun s => (s, BinTree.leaf)
    | BinTree.branch l x r =>
      andThen (enumerate_from l)
        (fun sl =>
          andThen (fun s => (s + 1, (s, x)))
            (fun sx =>
              andThen (enumerate_from r)
                (fun sr =>
                  fun s => (s, BinTree.branch sl sx sr)
                )
            )
        )
    let (_, t) := enumerate_from t 0
    t

#eval example_tree.enumerateAndThen

def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

def BinTree.enumerateInfix (t : BinTree α) : BinTree (Nat × α) :=
  let rec enumerate_from : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok BinTree.leaf
    | BinTree.branch l x r =>
      enumerate_from l ~~> fun sl =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      enumerate_from r ~~> fun sr =>
      ok (BinTree.branch sl (n, x) sr)
    (enumerate_from t 0).snd

#eval example_tree.enumerateInfix

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch l x r =>
    mapM f l >>= fun ml =>
    f x >>= fun mx =>
    mapM f r >>= fun mr =>
    pure (BinTree.branch ml mx mr)

def enumerate (v : α) : State Nat (Nat × α) :=
  get >>= fun n =>
  set (n + 1) >>= fun () =>
  pure (n, v)

#eval example_tree.mapM enumerate 0

def doEnumerate (v : α) : State Nat (Nat × α) := do
  let n ← get
  set (n + 1)
  pure (n, v)

def BinTree.doMapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | .leaf => pure .leaf
  | .branch l x r => do
    let ml ← doMapM f l
    let mx ← f x
    let mr ← doMapM f r
    pure (.branch ml mx mr)

#eval example_tree.doMapM doEnumerate 0

-- Programming with Dependent Types

-- Exercises from 8.1 Indexed Families

inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

--def IsListLengthN (xs : List α) (n : Nat) : Prop := xs.length == n

#eval ["Mount Hood",
 "Mount Jefferson",
 "South Sister"].zip ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]

def OregonPeaks : Vect String 3 :=
  .cons "Mount Hood" (
    .cons "Mount Jefferson" (
      .cons "South Sister" .nil
    )
  )

def DenmarkPeaks : Vect String 3 :=
  .cons "Møllehøj" (
    .cons "Yding Skovhøj" (
      .cons "Ejer Bavnehøj" .nil
    )
  )

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1

theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption

-- Tail recursion exercises
def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => helper xs (x :: acc)
  helper xs []

#eval Tail.reverse [1,2,3,4,5]

def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1

def Tail.length (xs : List α) : Nat :=
  let rec helper : List α → Nat → Nat
  | [], acc => acc
  | _ :: xs, acc => helper xs (acc + 1)
  helper xs 0

#eval Tail.length ["a", "b", "c", "d"]

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def Tail.factorial (n : Nat) : Nat :=
  let rec helper : Nat → Nat → Nat
    | 0, acc => acc
    | n + 1, acc => helper n (acc * (n + 1))
  helper n 1

#eval Tail.factorial 0
#eval Tail.factorial 1
#eval Tail.factorial 3

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def Tail.filter (p : α → Bool) (xs : List α) : List α :=
  let rec helper : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc =>
    if p x then
      helper xs (x :: acc)
    else
      helper xs acc
  Tail.reverse (helper xs [])

#eval Tail.filter (fun (x : Nat) => x > 3) [1,2,3,4,5]

def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + NonTail.sum xs

def Tail.sum (xs : List Nat) : Nat :=
  let rec helper : List Nat → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => helper xs (acc + x)
  helper xs 0

-- Tail recursion proofs

theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
  (n : Nat) → n + NonTail.sum xs = Tail.sum.helper xs n := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sum.helper]
    rw [←Nat.add_assoc]
    exact ih (n + y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  unfold Tail.sum
  rw [← Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0

theorem MyNat.zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ihp =>
    rw [Nat.add_succ]
    rw [ihp]

theorem MyNat.add_assoc (a b c : Nat) : a + b + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [MyNat.zero_add b]
    rw [MyNat.zero_add (b + c)]
  | succ n ihp =>
    simp [Nat.succ_add]
    exact ihp

theorem MyNat.add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ihp => rw [Nat.succ_add, Nat.add_succ, ihp]

theorem non_tail_reverse_eq_helper_accum (xs : List α) :
  (ys : List α) → NonTail.reverse xs ++ ys = Tail.reverse.helper xs ys := by
  induction xs with
  | nil =>
    intro ys
    rfl
  | cons x xs ihp =>
    intro ys
    unfold NonTail.reverse
    unfold Tail.reverse.helper
    rw [← ihp]
    simp [List.append_assoc]

theorem List.append_empty (xs : List α) : xs ++ [] = xs := by simp

theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
  funext α xs
  unfold Tail.reverse
  rw [← List.append_empty (NonTail.reverse xs)]
  exact non_tail_reverse_eq_helper_accum xs []

theorem tail_factorial_helper_eq (n : Nat) :
  (x : Nat) → NonTail.factorial n * x = Tail.factorial.helper n x := by
  induction n with
  | zero =>
    intro x
    simp [NonTail.factorial, Tail.factorial.helper]
  | succ n ihn =>
    intro x
    simp [NonTail.factorial, Tail.factorial.helper]
    rw [← ihn (x * (n + 1))]
    rw [Nat.mul_comm x (n + 1)]
    rw [Nat.mul_assoc]

theorem non_tail_factorial_eq_tail_factorial : NonTail.factorial = Tail.factorial := by
  funext n
  unfold Tail.factorial
  rw [← Nat.mul_one (NonTail.factorial n)]
  exact tail_factorial_helper_eq n 1

-- Arrays

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by findHelper arr p i => arr.size - i

def MyArray.reverse (arr : Array α) : Array α :=
  let rec helper (acc : Array α) : Nat → Array α :=
  if h :
  | 0 => acc
  | i + 1 => helper (acc.push arr[i]) i
  helper Array.empty arr.size
