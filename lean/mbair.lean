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
