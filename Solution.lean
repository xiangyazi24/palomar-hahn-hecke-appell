import PalomarHahnHeckeAppell

/-!
# Proved solution for the preliminary Palomar Challenge

The definitions intentionally duplicate the small trusted statement surface.
The proof is supplied by the extracted substantive development.
-/

namespace PalomarHahnHeckeAppell

def C2Twice (k : ℤ) : ℤ := k * (k - 1)

def C2 (k : ℤ) : ℤ := k * (k - 1) / 2

def delta (n p : ℤ) : ℤ := p * (2 * n + p)

def modulus (n p : ℤ) : ℤ := n * delta n p

def A0 (n p : ℤ) : ℤ := n * p * (2 * n + p + 1) / 2

def heckeExponent (n p r s : ℤ) : ℤ :=
  n * C2 r + (n + p) * r * s + n * C2 s

theorem row_exponent_identity (r t ell k n p : ℤ) :
    n * C2 t + n * C2 (r + (n + p) * ell) +
      (n + p) * t * (r + (n + p) * ell) +
      modulus n p * C2 k +
      ell * (modulus n p * (k - 1) + A0 n p - t * delta n p) =
    heckeExponent n p r (n * ell + t) + modulus n p * C2 (k + ell) := by
  simpa [C2, delta, modulus, A0, heckeExponent,
    QseriesFormalization.Pending.Ch10RootPairGeneral.C2,
    QseriesFormalization.Pending.Ch10RootPairGeneral.genDelta,
    QseriesFormalization.Pending.Ch10RootPairGeneral.genN,
    QseriesFormalization.Pending.Ch10RootPairGeneral.genA0,
    QseriesFormalization.Pending.Ch10RootPairGeneral.heckeExp] using
    QseriesFormalization.Pending.Ch10RootPairGeneral.row_exponent_identity
      r t ell k n p

end PalomarHahnHeckeAppell
