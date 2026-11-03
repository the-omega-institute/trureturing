using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/XuYangMillsRemainder/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/xuyang2026millsratio");
    private const string Quotation = "Moreover, inspired by Theorem 4.2, we propose the following conjecture. Conjecture 7.1 Let D_n(x, a) = Y_{a,a–2}(x) – (a – 1 + Σ_{k=1}^{n} (–1)^k u_k / x^{2k}), where u_k is defined by (3.7). Then x ↦ (–1)^n D_n(x, –1) is CM on (0, ∞).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Laplace kernels for the signed Xu–Yang Mills-ratio remainders.",
        H("The signed Mills-ratio remainders"), Blocks(
            Entry("CompletelyMonotoneOn", All("f", Arr, Eq(C("CompletelyMonotoneOn", V("f")), And(C("ContDiffOn", R, Infty, V("f"), C("Set.Ioi", new Formula.Number(0))), All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), Le(new Formula.Number(0), Mul(Pow(Neg(new Formula.Number(1)), V("m")), C("iteratedDeriv", V("m"), V("f"), V("x")))))))))),
                "The definition is C-infinity on the positive half-line together with the sign of every ordinary iterated derivative, exactly the complete-monotonicity condition.", DescribeRole.Definition, true),
            Entry("millsRatio", All("x", R, Eq(C("millsRatio", V("x")), Mul(C("Real.exp", Div(Pow(V("x"), new Formula.Number(2)), new Formula.Number(2))), TailIntegral(V("x"), "t", C("Real.exp", Neg(Div(Pow(V("t"), new Formula.Number(2)), new Formula.Number(2)))))))),
                "The Gaussian-tail normalization is R in the source, printed page 2. Extending the defining expression to every real x does not change its positive-domain values.", DescribeRole.Definition, true),
            Entry("Y", All("a", R, All("b", R, All("x", R, Eq(C("Y", V("a"), V("b"), V("x")), Add(Mul(Add(Pow(V("x"), new Formula.Number(2)), V("a")), Pow(C("millsRatio", V("x")), new Formula.Number(2))), Mul(Mul(V("b"), V("x")), C("millsRatio", V("x")))))))),
                "Equation (1.8), printed page 3, with its surrounding statement: “Note that all bounds of the form ϕ_{p,q,r}(x) can be derived from the inequality Y_{a,b}(x) := (x² + a)R²(x) + bxR(x) < (>) c for all x > 0, a, b ∈ ℝ, where c = lim_{x→0} Y_{a,b}(x) = aπ/2 or c = lim_{x→∞} Y_{a,b}(x) = b + 1.” Y is the displayed defining expression.", DescribeRole.Definition, true),
            Entry("u", All("k", N, All("a", R, All("b", R, Eq(C("u", V("k"), V("a"), V("b")), Add(Div(Mul(Mul(Add(V("b"), new Formula.Number(1)), Pow(new Formula.Number(2), V("k"))), C("Real.Gamma", Add(V("k"), Div(new Formula.Number(1), new Formula.Number(2))))), C("Real.Gamma", Div(new Formula.Number(1), new Formula.Number(2)))), Mul(Mul(Sub(V("k"), V("a")), C("Nat.factorial", C("Nat.sub", V("k"), new Formula.Number(1)))), SumRange("j", V("k"), Div(Mul(Pow(new Formula.Number(2), V("j")), C("Real.Gamma", Add(V("j"), Div(new Formula.Number(1), new Formula.Number(2))))), Mul(C("Real.Gamma", Div(new Formula.Number(1), new Formula.Number(2))), C("Nat.factorial", V("j"))))))))))),
                "Equation (3.7), printed page 6: “where u_n ≡ u_n(a, b) = (b + 1) 2^n Γ(n + 1/2)/Γ(1/2) + (n − a)(n − 1)! Σ_{k=0}^{n−1} 2^k Γ(k + 1/2)/(Γ(1/2) k!). In particular, u₁ = b + 2 − a, u₂ = 3b + 7 − 2a, u₃ = 15b + 36 − 7a, and u₄ = 105b − 36a + 249.” Natural indices in real arithmetic are coerced to real numbers; the Gamma factors remain in their original form. The factorial index Nat.sub(k,1) is natural subtraction, truncated at zero. It agrees with k-1 for every positive coefficient index used in the source.", DescribeRole.Definition, true),
            Entry("D", All("n", N, All("x", R, All("a", R, Eq(C("D", V("n"), V("x"), V("a")), Sub(C("Y", V("a"), Sub(V("a"), new Formula.Number(2)), V("x")), Add(Sub(V("a"), new Formula.Number(1)), SumIcc("k", new Formula.Number(1), V("n"), Div(Mul(Pow(Neg(new Formula.Number(1)), V("k")), C("u", V("k"), V("a"), Sub(V("a"), new Formula.Number(2)))), Pow(V("x"), Mul(new Formula.Number(2), V("k"))))))))))),
                "This is the finite asymptotic remainder appearing in Conjecture 7.1.", DescribeRole.Definition, true),
            Describe.Lean(DescribeId.Create("xu-yang-mills-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The complete-monotonicity assertion for every n at least two"),
                StatementSource.FromAuthor(Disp(Eq(V("claim"), All("n", N, Imp(Le(new Formula.Number(2), V("n")), C("CompletelyMonotoneOn", Lam("x", Mul(Pow(Neg(new Formula.Number(1)), V("n")), C("D", V("n"), V("x"), Neg(new Formula.Number(1))))))))))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (1.8), printed page 3, complete defining statement: “Note that all bounds of the form ϕ_{p,q,r}(x) can be derived from the inequality Y_{a,b}(x) := (x² + a)R²(x) + bxR(x) < (>) c for all x > 0, a, b ∈ ℝ, where c = lim_{x→0} Y_{a,b}(x) = aπ/2 or c = lim_{x→∞} Y_{a,b}(x) = b + 1.”")),
                    Paragraph(Text("Equation (3.7), printed page 6, complete defining statement: “where u_n ≡ u_n(a, b) = (b + 1) 2^n Γ(n + 1/2)/Γ(1/2) + (n – a)(n – 1)! Σ_{k=0}^{n–1} 2^k Γ(k + 1/2)/(Γ(1/2) k!). In particular, u₁ = b + 2 – a, u₂ = 3b + 7 – 2a, u₃ = 15b + 36 – 7a, and u₄ = 105b – 36a + 249.”")),
                    Paragraph(Text("Conjecture 7.1, printed page 27, complete statement with line breaks joined: “" + Quotation + "”")),
                    Paragraph(Text("The lower index is n≥2. The source coefficients at a=-1, b=-3 vanish at indices one and two, so D1 equals D2 and the signed index-one remainder is -D2. The definition uses C-infinity and the paper’s condition (-1)^m f^(m)≥0 for every natural m, including zero."))), DescribeRole.Definition),
            Entry("millsLaplace", All("x", R, Eq(C("millsRatio", V("x")), TailIntegral(new Formula.Number(0), "t", C("Real.exp", Sub(Neg(Mul(V("x"), V("t"))), Div(Pow(V("t"), new Formula.Number(2)), new Formula.Number(2))))))),
                "Translation by x in the Gaussian tail gives the positive-ray Laplace representation.", DescribeRole.Theorem),
            Entry("millsLaplaceIntegrable", All("x", R, Imp(Le(new Formula.Number(0), V("x")), C("MeasureTheory.IntegrableOn", Lam("t", C("Real.exp", Sub(Neg(Mul(V("x"), V("t"))), Div(Pow(V("t"), new Formula.Number(2)), new Formula.Number(2))))), C("Set.Ioi", new Formula.Number(0))))),
                "For nonnegative x the tilted Gaussian is dominated by the integrable Gaussian.", DescribeRole.Theorem),
            Entry("millsSquareConvolution", All("x", R, Imp(Le(new Formula.Number(0), V("x")), Eq(Pow(C("millsRatio", V("x")), new Formula.Number(2)), TailIntegral(new Formula.Number(0), "t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), IntervalIntegral(new Formula.Number(0), V("t"), "s", Mul(C("Real.exp", Neg(Div(Pow(V("s"), new Formula.Number(2)), new Formula.Number(2)))), C("Real.exp", Neg(Div(Pow(Sub(V("t"), V("s")), new Formula.Number(2)), new Formula.Number(2))))))))))),
                "The positive-ray convolution integral equals the product of the two Mills Laplace integrals.", DescribeRole.Theorem),
            Entry("convolutionClosed", All("t", R, Eq(IntervalIntegral(new Formula.Number(0), V("t"), "s", Mul(C("Real.exp", Neg(Div(Pow(V("s"), new Formula.Number(2)), new Formula.Number(2)))), C("Real.exp", Neg(Div(Pow(Sub(V("t"), V("s")), new Formula.Number(2)), new Formula.Number(2)))))), Mul(V("t"), UnitIntegral("v", C("Real.exp", Div(Neg(Mul(Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))), Pow(V("t"), new Formula.Number(2)))), new Formula.Number(4))))))),
                "An affine substitution and evenness of the Gaussian give the closed convolution kernel.", DescribeRole.Theorem),
            Entry("moment", All("f", Arr, All("m", N, All("x", R, Eq(C("moment", V("f"), V("m"), V("x")), TailIntegral(new Formula.Number(0), "t", Mul(Mul(Pow(Neg(V("t")), V("m")), C("Real.exp", Neg(Mul(V("x"), V("t"))))), C("f", V("t")))))))),
                "The signed Laplace moments give the derivatives of the zeroth moment.", DescribeRole.Definition),
            Entry("momentDeriv", All("f", Arr, Imp(C("Continuous", V("f")), Imp(All("t", R, Imp(Lt(new Formula.Number(0), V("t")), Le(new Formula.Number(0), C("f", V("t"))))), Imp(All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), C("MeasureTheory.IntegrableOn", Lam("t", Mul(Mul(Pow(V("t"), V("m")), C("Real.exp", Neg(Mul(V("x"), V("t"))))), C("f", V("t")))), C("Set.Ioi", new Formula.Number(0)))))), All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), C("HasDerivAt", C("moment", V("f"), V("m")), C("moment", V("f"), Add(V("m"), new Formula.Number(1)), V("x")), V("x"))))))))),
                "Domination at x/2 justifies differentiation under the integral for every moment.", DescribeRole.Theorem),
            Entry("momentIterated", All("f", Arr, Imp(C("Continuous", V("f")), Imp(All("t", R, Imp(Lt(new Formula.Number(0), V("t")), Le(new Formula.Number(0), C("f", V("t"))))), Imp(All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), C("MeasureTheory.IntegrableOn", Lam("t", Mul(Mul(Pow(V("t"), V("m")), C("Real.exp", Neg(Mul(V("x"), V("t"))))), C("f", V("t")))), C("Set.Ioi", new Formula.Number(0)))))), All("m", N, C("Set.EqOn", C("iteratedDeriv", V("m"), C("moment", V("f"), new Formula.Number(0))), C("moment", V("f"), V("m")), C("Set.Ioi", new Formula.Number(0)))))))),
                "The derivative identity iterates on the open positive half-line.", DescribeRole.Theorem),
            Entry("laplaceCM", All("f", Arr, Imp(C("Continuous", V("f")), Imp(All("t", R, Imp(Lt(new Formula.Number(0), V("t")), Le(new Formula.Number(0), C("f", V("t"))))), Imp(All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), C("MeasureTheory.IntegrableOn", Lam("t", Mul(Mul(Pow(V("t"), V("m")), C("Real.exp", Neg(Mul(V("x"), V("t"))))), C("f", V("t")))), C("Set.Ioi", new Formula.Number(0)))))), C("CompletelyMonotoneOn", C("moment", V("f"), new Formula.Number(0))))))),
                "Smoothness follows from differentiation of every moment, and the two sign factors cancel inside the nonnegative integral.", DescribeRole.Theorem),
            Entry("coeff", All("k", N, Eq(C("coeff", V("k")), Div(Mul(Pow(new Formula.Number(2), V("k")), C("Real.Gamma", Add(V("k"), Div(new Formula.Number(1), new Formula.Number(2))))), C("Real.Gamma", Div(new Formula.Number(1), new Formula.Number(2)))))),
                "The half-integer Gamma coefficient abbreviates the repeated factor in (3.7).", DescribeRole.Definition),
            Entry("intPow", All("m", N, Eq(C("intPow", V("m")), UnitIntegral("v", Pow(Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))), V("m"))))),
                "These compact polynomial integrals encode the coefficient sum.", DescribeRole.Definition),
            Entry("intWeight", All("m", N, Eq(C("intWeight", V("m")), UnitIntegral("v", Mul(Mul(Pow(V("v"), new Formula.Number(2)), Sub(new Formula.Number(1), Pow(V("v"), new Formula.Number(2)))), Pow(Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))), V("m")))))),
                "The weight is nonnegative on the unit interval and is the same weight that occurs in K.", DescribeRole.Definition),
            Entry("intPow_rec", All("m", N, Eq(Sub(Mul(Add(Mul(new Formula.Number(2), V("m")), new Formula.Number(3)), C("intPow", Add(V("m"), new Formula.Number(1)))), Mul(Mul(new Formula.Number(2), Add(V("m"), new Formula.Number(1))), C("intPow", V("m")))), Pow(new Formula.Number(2), Add(V("m"), new Formula.Number(1))))),
                "Integrate the derivative of v times (1+v-squared) to the power m+1.", DescribeRole.Theorem),
            Entry("coeff_zero", Eq(C("coeff", new Formula.Number(0)), new Formula.Number(1)),
                "The Gamma factors cancel at index zero.", DescribeRole.Theorem),
            Entry("coeff_rec", All("m", N, Eq(C("coeff", Add(V("m"), new Formula.Number(1))), Mul(Add(Mul(new Formula.Number(2), V("m")), new Formula.Number(1)), C("coeff", V("m"))))),
                "The Gamma recurrence gives the odd-factor coefficient recurrence.", DescribeRole.Theorem),
            Entry("coeff_sum", All("m", N, Eq(SumRange("j", Add(V("m"), new Formula.Number(1)), Div(C("coeff", V("j")), C("Nat.factorial", V("j")))), Mul(Div(C("coeff", Add(V("m"), new Formula.Number(1))), Mul(Pow(new Formula.Number(2), V("m")), C("Nat.factorial", V("m")))), C("intPow", V("m"))))),
                "Induction combines the compact integral recurrence with the Gamma coefficient recurrence.", DescribeRole.Theorem),
            Entry("intWeight_eq", All("m", N, Eq(Mul(Mul(Mul(new Formula.Number(2), Add(V("m"), new Formula.Number(1))), Add(V("m"), new Formula.Number(2))), C("intWeight", V("m"))), Sub(Pow(new Formula.Number(2), Add(V("m"), new Formula.Number(3))), Mul(Add(V("m"), new Formula.Number(4)), C("intPow", Add(V("m"), new Formula.Number(2))))))),
                "Expanding the polynomial weight and applying two consecutive integral recurrences evaluates the weighted combination.", DescribeRole.Theorem),
            Entry("coeff_factorial", All("m", N, Eq(Mul(C("coeff", Add(V("m"), new Formula.Number(1))), Mul(Pow(new Formula.Number(2), V("m")), C("Nat.factorial", V("m")))), C("Nat.factorial", Add(Mul(new Formula.Number(2), V("m")), new Formula.Number(1))))),
                "Mathlib’s half-integer Gamma formula and the factorial–double-factorial identity convert the normalization into an odd factorial.", DescribeRole.Theorem),
            Entry("u_kernel_coeff", All("m", N, Eq(C("u", Add(V("m"), new Formula.Number(3)), Neg(new Formula.Number(1)), Neg(new Formula.Number(3))), Mul(Neg(Div(Mul(Mul(C("coeff", Add(V("m"), new Formula.Number(3))), Add(V("m"), new Formula.Number(1))), Add(V("m"), new Formula.Number(2))), Pow(new Formula.Number(2), Add(V("m"), new Formula.Number(1))))), C("intWeight", V("m"))))),
                "The original coefficients at a=-1, b=-3 are negative weighted kernel coefficients.", DescribeRole.Theorem),
            Entry("u_kernel_factorial", All("m", N, Eq(C("u", Add(V("m"), new Formula.Number(3)), Neg(new Formula.Number(1)), Neg(new Formula.Number(3))), Mul(Div(Neg(C("Nat.factorial", Add(Mul(new Formula.Number(2), V("m")), new Formula.Number(5)))), Mul(Mul(new Formula.Number(8), Pow(new Formula.Number(4), V("m"))), C("Nat.factorial", V("m")))), C("intWeight", V("m"))))),
                "The equivalent factorial normalization is (2m+5)! divided by 8 times 4 to the m times m!. This is the normalization obtained by integrating the monomial Laplace term.", DescribeRole.Theorem),
            Entry("u_special", All("m", N, Eq(C("u", Add(V("m"), new Formula.Number(1)), Neg(new Formula.Number(1)), Neg(new Formula.Number(3))), Add(Mul(Neg(new Formula.Number(2)), C("coeff", Add(V("m"), new Formula.Number(1)))), Mul(Mul(Add(V("m"), new Formula.Number(2)), C("Nat.factorial", V("m"))), SumRange("j", Add(V("m"), new Formula.Number(1)), Div(C("coeff", V("j")), C("Nat.factorial", V("j")))))))),
                "Substituting a=-1 and b=-3 isolates the common Gamma coefficient sum.", DescribeRole.Theorem),
            Entry("u_one_zero", Eq(C("u", new Formula.Number(1), Neg(new Formula.Number(1)), Neg(new Formula.Number(3))), new Formula.Number(0)),
                "The coefficient of x to the power -2 vanishes.", DescribeRole.Theorem),
            Entry("u_two_zero", Eq(C("u", new Formula.Number(2), Neg(new Formula.Number(1)), Neg(new Formula.Number(3))), new Formula.Number(0)),
                "The coefficient of x to the power -4 also vanishes.", DescribeRole.Theorem),
            Entry("D_rec", All("r", N, All("x", R, Eq(C("D", Add(V("r"), new Formula.Number(3)), V("x"), Neg(new Formula.Number(1))), Sub(C("D", Add(V("r"), new Formula.Number(2)), V("x"), Neg(new Formula.Number(1))), Div(Mul(Pow(Neg(new Formula.Number(1)), Add(V("r"), new Formula.Number(3))), C("u", Add(V("r"), new Formula.Number(3)), Neg(new Formula.Number(1)), Neg(new Formula.Number(3)))), Pow(V("x"), Mul(new Formula.Number(2), Add(V("r"), new Formula.Number(3))))))))),
                "Adding the top index to the finite sum gives the recurrence for successive remainders.", DescribeRole.Theorem),
            Entry("D_two", All("x", R, Eq(C("D", new Formula.Number(2), V("x"), Neg(new Formula.Number(1))), Add(Sub(Mul(Sub(Pow(V("x"), new Formula.Number(2)), new Formula.Number(1)), Pow(C("millsRatio", V("x")), new Formula.Number(2))), Mul(Mul(new Formula.Number(3), V("x")), C("millsRatio", V("x")))), new Formula.Number(2)))),
                "The first two vanishing coefficients identify D at index two with the basic expression H.", DescribeRole.Theorem),
            Entry("J", All("p", Arr, All("t", R, Eq(C("J", V("p"), V("t")), UnitIntegral("v", Mul(C("p", V("v")), C("Real.exp", Div(Neg(Mul(Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))), Pow(V("t"), new Formula.Number(2)))), new Formula.Number(4)))))))),
                "This Gaussian average uses the fixed unit interval.", DescribeRole.Definition),
            Entry("q0", All("t", R, Eq(C("q0", V("t")), Mul(V("t"), C("J", C("Function.const", R, new Formula.Number(1)), V("t"))))),
                "The closed convolution kernel is q0.", DescribeRole.Definition),
            Entry("q1", All("t", R, Eq(C("q1", V("t")), Sub(C("J", C("Function.const", R, new Formula.Number(1)), V("t")), Mul(Div(Pow(V("t"), new Formula.Number(2)), new Formula.Number(2)), C("J", Lam("v", Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2)))), V("t")))))),
                "The first derivative of the convolution kernel has this explicit form.", DescribeRole.Definition),
            Entry("q2", All("t", R, Eq(C("q2", V("t")), Sub(Mul(Div(Pow(V("t"), new Formula.Number(3)), new Formula.Number(4)), C("J", Lam("v", Pow(Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))), new Formula.Number(2))), V("t"))), Mul(Div(Mul(new Formula.Number(3), V("t")), new Formula.Number(2)), C("J", Lam("v", Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2)))), V("t")))))),
                "The second derivative is a difference of two polynomial Gaussian averages.", DescribeRole.Definition),
            Entry("K", All("t", R, Eq(C("K", V("t")), Mul(Div(Pow(V("t"), new Formula.Number(5)), new Formula.Number(8)), C("J", Lam("v", Mul(Pow(V("v"), new Formula.Number(2)), Sub(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))))), V("t"))))),
                "K is the positive Gaussian kernel for the basic Mills-ratio remainder.", DescribeRole.Definition),
            Entry("JDeriv", All("p", Arr, Imp(C("Continuous", V("p")), All("t", R, C("HasDerivAt", C("J", V("p")), Mul(Neg(Div(V("t"), new Formula.Number(2))), C("J", Lam("v", Mul(C("p", V("v")), Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))))), V("t"))), V("t"))))),
                "Differentiation under the fixed interval integral, justified by a continuous derivative on compact parameter rectangles, inserts the factor -(t/2)(1+v-squared) into the Gaussian average.", DescribeRole.Theorem),
            Entry("q0Deriv", All("t", R, C("HasDerivAt", C("q0"), C("q1", V("t")), V("t"))),
                "The product rule gives q1 as the derivative of q0.", DescribeRole.Theorem),
            Entry("q1Deriv", All("t", R, C("HasDerivAt", C("q1"), C("q2", V("t")), V("t"))),
                "A second product-rule calculation gives q2.", DescribeRole.Theorem),
            Entry("kernelIdentity", All("t", R, Eq(Add(Sub(C("q2", V("t")), C("q0", V("t"))), Mul(Mul(new Formula.Number(3), V("t")), C("Real.exp", Neg(Div(Pow(V("t"), new Formula.Number(2)), new Formula.Number(2)))))), C("K", V("t")))),
                "Two applications of the fundamental theorem in the unit-interval variable remove the lower-degree Gaussian terms, leaving the nonnegative weight v-squared times (1-v-squared).", DescribeRole.Theorem),
            Entry("JBound", All("p", Arr, Imp(C("Continuous", V("p")), Ex("C", R, And(Le(new Formula.Number(0), V("C")), All("t", R, Le(Norm(C("J", V("p"), V("t"))), V("C"))))))),
                "The Gaussian factor is at most one, so compact boundedness of p gives a uniform bound on J.", DescribeRole.Theorem),
            Entry("JMomentIntegrable", All("p", Arr, Imp(C("Continuous", V("p")), All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), C("MeasureTheory.IntegrableOn", Lam("t", Mul(Mul(Pow(V("t"), V("m")), C("Real.exp", Neg(Mul(V("x"), V("t"))))), C("J", V("p"), V("t")))), C("Set.Ioi", new Formula.Number(0)))))))),
                "The uniform bound on J reduces integrability to polynomial exponential moments.", DescribeRole.Theorem),
            Entry("JMomentTendsto", All("p", Arr, Imp(C("Continuous", V("p")), All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), C("Filter.Tendsto", Lam("t", Mul(Mul(Pow(V("t"), V("m")), C("Real.exp", Neg(Mul(V("x"), V("t"))))), C("J", V("p"), V("t")))), C("Filter.atTop"), C("nhds", new Formula.Number(0)))))))),
                "The polynomial exponential envelope tends to zero and controls all integration-by-parts boundary terms.", DescribeRole.Theorem),
            Entry("laplaceIBP", All("f", Arr, All("g", Arr, All("x", R, Imp(All("t", R, C("HasDerivAt", V("f"), C("g", V("t")), V("t"))), Imp(C("MeasureTheory.IntegrableOn", Lam("t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("f", V("t")))), C("Set.Ioi", new Formula.Number(0))), Imp(C("MeasureTheory.IntegrableOn", Lam("t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("g", V("t")))), C("Set.Ioi", new Formula.Number(0))), Imp(C("Filter.Tendsto", Lam("t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("f", V("t")))), C("Filter.atTop"), C("nhds", new Formula.Number(0))), Eq(TailIntegral(new Formula.Number(0), "t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("g", V("t")))), Sub(Mul(V("x"), TailIntegral(new Formula.Number(0), "t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("f", V("t"))))), C("f", new Formula.Number(0))))))))))),
                "The fundamental theorem on the positive ray gives integration by parts when the weighted function and derivative are integrable and the infinite boundary vanishes.", DescribeRole.Theorem),
            Entry("kernelLaplace", All("x", R, Imp(Lt(new Formula.Number(0), V("x")), All("r", R, Imp(Eq(V("r"), TailIntegral(new Formula.Number(0), "t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("Real.exp", Neg(Div(Pow(V("t"), new Formula.Number(2)), new Formula.Number(2))))))), Imp(Eq(Pow(V("r"), new Formula.Number(2)), TailIntegral(new Formula.Number(0), "t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("q0", V("t"))))), Eq(Add(Sub(Mul(Sub(Pow(V("x"), new Formula.Number(2)), new Formula.Number(1)), Pow(V("r"), new Formula.Number(2))), Mul(Mul(new Formula.Number(3), V("x")), V("r"))), new Formula.Number(2)), TailIntegral(new Formula.Number(0), "t", Mul(C("Real.exp", Neg(Mul(V("x"), V("t")))), C("K", V("t")))))))))),
                "Integrating by parts twice transfers x-squared from the Laplace transform to q2. The Gaussian derivative accounts for the linear Mills term, and the kernel identity yields K.", DescribeRole.Theorem),
            Entry("expRemainder", All("r", N, All("v", R, Eq(C("expRemainder", V("r"), V("v")), Mul(Pow(Neg(new Formula.Number(1)), V("r")), Add(C("D5.S3.Analytic.ExpRemainderDifferences.R", V("r"), Neg(V("v"))), Div(Pow(Neg(V("v")), V("r")), C("Nat.factorial", V("r")))))))),
                "The exponential remainder R through degree r is evaluated at -v and its top Taylor monomial is restored, then multiplied by the alternating sign. This gives the signed remainder after r terms.", DescribeRole.Definition),
            Entry("expRemainder_eq", All("r", N, All("v", R, Eq(C("expRemainder", V("r"), V("v")), Mul(Pow(Neg(new Formula.Number(1)), V("r")), Sub(C("Real.exp", Neg(V("v"))), SumRange("j", V("r"), Div(Pow(Neg(V("v")), V("j")), C("Nat.factorial", V("j"))))))))),
                "Removing the last term from the degree-r Taylor sum gives the finite-remainder expression for every r, including zero, when the sum is empty and the remainder equals exp(-v).", DescribeRole.Theorem),
            Entry("expRemainderBounds", All("r", N, All("v", R, Imp(Le(new Formula.Number(0), V("v")), And(Le(new Formula.Number(0), C("expRemainder", V("r"), V("v"))), Le(C("expRemainder", V("r"), V("v")), Div(Pow(V("v"), V("r")), C("Nat.factorial", V("r")))))))),
                "Taylor’s theorem with a Lagrange remainder gives positivity and the polynomial upper bound. The order-zero case uses exp(-v) between zero and one.", DescribeRole.Theorem),
            Entry("expRemainderContinuous", All("r", N, C("Continuous", C("expRemainder", V("r")))),
                "The finite sum and exponential are continuous.", DescribeRole.Theorem),
            Entry("expRemainderRec", All("r", N, All("v", R, Eq(C("expRemainder", Add(V("r"), new Formula.Number(1)), V("v")), Sub(Div(Pow(V("v"), V("r")), C("Nat.factorial", V("r"))), C("expRemainder", V("r"), V("v")))))),
                "The next signed remainder is the current Taylor monomial minus the preceding signed remainder.", DescribeRole.Theorem),
            Entry("remainderKernel", All("r", N, All("t", R, Eq(C("remainderKernel", V("r"), V("t")), Mul(Div(Pow(V("t"), new Formula.Number(5)), new Formula.Number(8)), UnitIntegral("v", Mul(Mul(Pow(V("v"), new Formula.Number(2)), Sub(new Formula.Number(1), Pow(V("v"), new Formula.Number(2)))), C("expRemainder", V("r"), Div(Mul(Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))), Pow(V("t"), new Formula.Number(2))), new Formula.Number(4))))))))),
                "The kernel for every truncation index replaces the Gaussian factor of K by its signed finite Taylor remainder.", DescribeRole.Definition),
            Entry("remainderKernelContinuous", All("r", N, C("Continuous", C("remainderKernel", V("r")))),
                "Continuous dependence of an integral over the compact unit interval gives continuity of each remainder kernel.", DescribeRole.Theorem),
            Entry("remainderKernelBounds", All("r", N, All("t", R, Imp(Le(new Formula.Number(0), V("t")), And(Le(new Formula.Number(0), C("remainderKernel", V("r"), V("t"))), Le(C("remainderKernel", V("r"), V("t")), Pow(V("t"), Add(Mul(new Formula.Number(2), V("r")), new Formula.Number(5)))))))),
                "The unit-interval weight lies between zero and one, and the Taylor remainder bound gives a polynomial envelope for the kernel.", DescribeRole.Theorem),
            Entry("remainderKernelMoments", All("r", N, All("m", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), C("MeasureTheory.IntegrableOn", Lam("t", Mul(Mul(Pow(V("t"), V("m")), C("Real.exp", Neg(Mul(V("x"), V("t"))))), C("remainderKernel", V("r"), V("t")))), C("Set.Ioi", new Formula.Number(0))))))),
                "The polynomial kernel envelope gives integrability after multiplication by every additional moment and positive-rate exponential.", DescribeRole.Theorem),
            Entry("remainderKernelRec", All("r", N, All("t", R, Eq(C("remainderKernel", Add(V("r"), new Formula.Number(1)), V("t")), Sub(Mul(Div(Pow(V("t"), Add(Mul(new Formula.Number(2), V("r")), new Formula.Number(5))), Mul(Mul(new Formula.Number(8), Pow(new Formula.Number(4), V("r"))), C("Nat.factorial", V("r")))), UnitIntegral("v", Mul(Mul(Pow(V("v"), new Formula.Number(2)), Sub(new Formula.Number(1), Pow(V("v"), new Formula.Number(2)))), Pow(Add(new Formula.Number(1), Pow(V("v"), new Formula.Number(2))), V("r"))))), C("remainderKernel", V("r"), V("t")))))),
                "The exponential-remainder recurrence gives the kernel recurrence with the same compact polynomial moment as the source coefficient.", DescribeRole.Theorem),
            Entry("remainderLaplaceRec", All("r", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), Eq(C("moment", C("remainderKernel", Add(V("r"), new Formula.Number(1))), new Formula.Number(0), V("x")), Sub(Div(Mul(Div(C("Nat.factorial", Add(Mul(new Formula.Number(2), V("r")), new Formula.Number(5))), Mul(Mul(new Formula.Number(8), Pow(new Formula.Number(4), V("r"))), C("Nat.factorial", V("r")))), C("intWeight", V("r"))), Pow(V("x"), Add(Mul(new Formula.Number(2), V("r")), new Formula.Number(6)))), C("moment", C("remainderKernel", V("r")), new Formula.Number(0), V("x"))))))),
                "Integrating the kernel recurrence evaluates its monomial by the Gamma integral and gives the recurrence for successive Laplace remainders.", DescribeRole.Theorem),
            Entry("remainderRepresentation", All("r", N, All("x", R, Imp(Lt(new Formula.Number(0), V("x")), Eq(Mul(Pow(Neg(new Formula.Number(1)), V("r")), C("D", Add(V("r"), new Formula.Number(2)), V("x"), Neg(new Formula.Number(1)))), C("moment", C("remainderKernel", V("r")), new Formula.Number(0), V("x")))))),
                "The basic kernel identity gives the order-zero case. Induction combines the coefficient identity with the finite remainder recurrence to obtain the exact positive Laplace representation at every truncation index.", DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("xu-yang-mills-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Complete monotonicity of every signed remainder"),
                StatementSource.FromAuthor(Disp(V("claim"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n≥2 the signed remainder has a nonnegative Laplace kernel. Its polynomial envelope makes every exponentially weighted moment integrable. Differentiation under the integral gives C-infinity smoothness and the sign of every derivative on the positive half-line."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("xu-yang-2026-mills-remainder-cm"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Entry(string name, Formula statement, string text, DescribeRole role, bool source = false) =>
        Describe.Lean(DescribeId.Create("xu-yang-mills-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace('_', ' ')),
            StatementSource.FromAuthor(Disp(statement)),
            source ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Arr => new Formula.TypeArrow(R, R);
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Ex(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula C(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.')) { if (parts.Count > 0) parts.Add(Dot); parts.Add(V(word)); }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Lam(string n, Formula body) => Seq(V(n), Colon, Sp, R, Mapsto, Sp, body);
    private static Formula TailIntegral(Formula a, string n, Formula body) => C("MeasureTheory.integral", C("Measure.restrict", C("volume"), C("Set.Ioi", a)), Lam(n, body));
    private static Formula UnitIntegral(string n, Formula body) => IntervalIntegral(new Formula.Number(0), new Formula.Number(1), n, body);
    private static Formula IntervalIntegral(Formula a, Formula b, string n, Formula body) => C("intervalIntegral", Lam(n, body), a, b, C("volume"));
    private static Formula SumRange(string n, Formula limit, Formula body) => Seq(new Formula.Subscript(Sum, Seq(V(n), Sp, InMacro, Sp, C("Finset.range", limit))), Sp, Parenthesized(body));
    private static Formula SumIcc(string n, Formula a, Formula b, Formula body) => Seq(new Formula.Subscript(Sum, Seq(V(n), Sp, InMacro, Sp, C("Finset.Icc", a, b))), Sp, Parenthesized(body));
}
