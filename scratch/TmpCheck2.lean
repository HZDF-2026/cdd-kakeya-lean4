import CddFormalization.RH_WeilFormula

open MeasureTheory
open scoped FourierTransform

#check @Real.fourier_eq'
#check @fourierInv_eq_fourier_neg
#check @MeasureTheory.Integrable.fourierInv_fourier_eq
example : True := trivial
