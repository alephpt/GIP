import Gen.ZetaEvaluation

open Gen.ZetaEvaluation

-- Test p-adic valuation
#eval p_adic_val 2 8   -- 3 (since 2³ = 8)
#eval p_adic_val 2 12  -- 2 (since 2² | 12 but 2³ ∤ 12)
#eval p_adic_val 3 27  -- 3 (since 3³ = 27)
#eval p_adic_val 5 10  -- 1 (since 5¹ | 10)

-- Test partial euler factors
#eval partial_euler_factor 2 4   
#eval partial_euler_factor 2 8   
#eval partial_euler_factor 3 9   

-- Test main zeta computation
#eval compute_zeta_gen 1
#eval compute_zeta_gen 2
#eval compute_zeta_gen 3
#eval compute_zeta_gen 4
#eval compute_zeta_gen 5
#eval compute_zeta_gen 6
#eval compute_zeta_gen 10
#eval compute_zeta_gen 12
