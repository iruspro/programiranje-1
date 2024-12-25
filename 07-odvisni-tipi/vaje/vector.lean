-- Vzamemo stvari iz predavanj
set_option autoImplicit false

inductive Naravno : Type where
  | nic : Naravno
  | naslednik : Naravno → Naravno
deriving Repr


def plus : Naravno → Naravno → Naravno :=
  fun m n =>
    match m with
    | Naravno.nic => n
    | Naravno.naslednik m' =>
        Naravno.naslednik (plus m' n)

-- Vektorji

inductive Vektor : Type → Naravno → Type where
  | prazen : {A : Type} → Vektor A Naravno.nic
  | sestavljen : {A : Type} → {n : Naravno} → A → Vektor A n → Vektor A (Naravno.naslednik n)
deriving Repr

#check (Vektor.sestavljen "a" (Vektor.sestavljen "b" (Vektor.prazen)))

def stakni_vektorja : {A : Type} → {m n : Naravno} → Vektor A m → Vektor A n → Vektor A (plus m n) :=
  fun {A : Type} {m n : Naravno} (xs : Vektor A m) (ys : Vektor A n) =>
    match xs with
    | Vektor.prazen => ys
    | Vektor.sestavljen x xs' => Vektor.sestavljen x (stakni_vektorja xs' ys)


-- Sedaj lahko definiramo `lookup`, ki ne bo nikoli povzročil napake.
inductive Finite : Naravno -> Type where
  | fzero : {n : Naravno} -> Finite (Naravno.naslednik n)
  | fsucc : {n : Naravno} -> Finite n -> Finite (Naravno.naslednik n)
deriving Repr


def lookup {A : Type} {n : Naravno} : Vektor A n -> Finite n -> A :=
  fun xs i =>
    match xs, i with
    | Vektor.sestavljen x _, Finite.fzero => x
    | Vektor.sestavljen _ xs', Finite.fsucc i' => lookup xs' i'

#check Finite.fsucc (Finite.fsucc (Finite.fzero))
#eval lookup (Vektor.sestavljen "a" (Vektor.sestavljen "b" (Vektor.sestavljen "c" (Vektor.prazen)))) (Finite.fsucc (Finite.fsucc (Finite.fzero)))


-- Včasih enakost tipov ni takoj očitna in jo moramo izpeljati
-- Dopolnite naslednjo definicijo, vse potrebne leme pa dokažite kar s taktiko `sorry`.

def plus_zero (n : Naravno) : (plus n Naravno.nic) = n := by
  induction n with
  | nic =>
    rw [plus]
  | naslednik d hd =>
    rw [plus]
    rw [hd]

def plus_add_suc (m n : Naravno) : (plus m (Naravno.naslednik n)) = (Naravno.naslednik (plus m n)) := by
  induction m with
  | nic =>
    repeat rw [plus]
  | naslednik d hd =>
    rw [plus]
    rw [hd]
    rw [← plus]

def plus_comm (m n : Naravno) : (plus m n) = (plus n m) := by
  induction m with
  | nic =>
    rw [plus]
    rw [plus_zero]
  | naslednik d hd =>
    rw [plus]
    rw [plus_add_suc]
    rw [hd]

-- xs ys
-- xs @ ys : Vector A (n + m)
-- xs @ ys : Vector A (m + n)
def stakni_vektorja' : {A : Type} → {m n : Naravno} → Vektor A m → Vektor A n → Vektor A (plus n m) := by
  intros t m n xs ys
  cases xs with
  | prazen =>
    rw [plus_zero]
    exact ys
  | sestavljen x xs' =>
    have v := Vektor.sestavljen x (stakni_vektorja' xs' ys)
    rw [plus_add_suc]
    exact v


-- Uporabite samo definicijo `stakni_vektorja'` in taktike `rw` in `exact`.
def stakni_vektorja'' : {A : Type} → {m n : Naravno} → Vektor A m → Vektor A n → Vektor A (plus m n) := by
  intros t m n xs ys
  rw [plus_comm]
  have v := stakni_vektorja' xs ys
  exact v


#print stakni_vektorja''
