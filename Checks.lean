import PsiZooProofs

/-!
Run `lake env lean Checks.lean` after `lake build` to display the central
statements and their foundational axiom dependencies. This file adds no axioms.
-/

#check PsiZoo.regionProbability_partition_sum_one
#check PsiZoo.spatial_region_probability_sum
#check PsiZoo.gaussianBarrier_eq_amplitude_iff
#check PsiZoo.stampPotential_bounds
#check PsiZoo.gridHamiltonianMatrix_decomposition
#check PsiZoo.cayleyLeft_isUnit
#check PsiZoo.hermitianCayley_mem_unitaryGroup
#check PsiZoo.hermitianCayley_iterate_normalized
#check PsiZoo.crankNicolsonEvolution_energy
#check PsiZoo.normalize_coordinateProjection

#print axioms PsiZoo.regionProbability_partition_sum_one
#print axioms PsiZoo.gaussianBarrier_eq_amplitude_iff
#print axioms PsiZoo.stampPotential_bounds
#print axioms PsiZoo.gridHamiltonianMatrix_decomposition
#print axioms PsiZoo.cayleyLeft_isUnit
#print axioms PsiZoo.hermitianCayley_mem_unitaryGroup
#print axioms PsiZoo.hermitianCayley_iterate_normalized
#print axioms PsiZoo.crankNicolsonEvolution_energy
#print axioms PsiZoo.hermitianCayley_neg_time
#print axioms PsiZoo.normalize_coordinateProjection
