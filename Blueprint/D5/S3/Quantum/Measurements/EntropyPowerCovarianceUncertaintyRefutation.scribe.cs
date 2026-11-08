using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class EntropyPowerCovarianceUncertaintyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Entropy/hertzjabbourcerf2017entropypower");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An equal mixture of two displaced coherent states violates the covariance-corrected quadrature entropy inequality in units with Planck's constant equal to one.",
        H("A Gaussian-mixture counterexample to covariance-corrected entropy uncertainty"),
        Blocks(
            Definition("gaussianWigner", "The one-mode Gaussian Wigner density", GaussianWignerFormula(),
                "The mean is (μx, μp), and the covariance matrix has diagonal entries a and c and off-diagonal entry b. "
                    + "Its determinant is ac − b². For a > 0, c > 0 and ac − b² ≥ 1/4, this is the normalized Wigner density of a physical one-mode Gaussian state with Planck's constant equal to one. "
                    + "The defining expression itself is a total real function and imposes none of those inequalities. "
                    + "The covariance convention is that of Section II.A of Hertz, Jabbour and Cerf, arXiv:1702.07286v2, EP-Unc-Rel-8.tex, lines 108–117."),
            Definition("marginalX", "The position marginal", MarginalFormula(true),
                "Integrating W over p gives its x marginal. For a Wigner function this is the probability density of the x quadrature, "
                    + "as in Section II.B, EP-Unc-Rel-8.tex, line 161. The definition takes any real function W of two real variables."),
            Definition("marginalP", "The momentum marginal", MarginalFormula(false),
                "Integrating W over x gives its p marginal. For a Wigner function this is the probability density of the p quadrature, "
                    + "as in Section II.B, EP-Unc-Rel-8.tex, line 161. All integrals here use Lebesgue volume."),
            Definition("densityEntropy", "Differential entropy", DensityEntropyFormula(),
                "Differential entropy is minus the integral of f times its natural logarithm. "
                    + "This is the convention in Section II.B, EP-Unc-Rel-8.tex, lines 155–159. "
                    + "The expression is defined for every real function f; the uncertainty statement separately requires integrability of the entropy integrands."),
            Definition("meanX", "The first position moment", MeanFormula(true),
                "The position mean is the phase-space integral of the first coordinate against W. "
                    + "For a normalized Wigner density this represents the quadrature mean used in Section II.A, EP-Unc-Rel-8.tex, line 108."),
            Definition("meanP", "The first momentum moment", MeanFormula(false),
                "The momentum mean is the phase-space integral of the second coordinate against W. "
                    + "It represents the second quadrature mean in Section II.A, EP-Unc-Rel-8.tex, line 108."),
            Definition("covarianceXX", "The central position second moment", CovarianceFormula("covarianceXX", true, false),
                "The position variance is the integral of the squared deviation from meanX W against W. "
                    + "This is the central-moment convention of Section II.A, EP-Unc-Rel-8.tex, lines 108–116, expressed on phase space."),
            Definition("covariancePP", "The central momentum second moment", CovarianceFormula("covariancePP", false, true),
                "The momentum variance is the integral of the squared deviation from meanP W against W. "
                    + "It is the second diagonal entry of the covariance matrix in Section II.A, EP-Unc-Rel-8.tex, lines 108–116."),
            Definition("covarianceXP", "The central cross moment", CovarianceFormula("covarianceXP", true, true),
                "The cross covariance integrates the product of the two centered coordinates against W. "
                    + "For a Wigner function this is the symmetrized quadrature covariance defined in Section II.A, EP-Unc-Rel-8.tex, line 117."),
            Describe.Lean(
                DescribeId.Create("entropy-power-covariance-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The covariance-corrected inequality for finite Gaussian mixtures"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimProposition()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Section III.B, EP-Unc-Rel-8.tex, lines 281–290, proposes subtracting the Gaussian mutual information from the sum of the two quadrature entropies and bounding the difference below by ln(πeℏ). "
                        + "The all-state assertion is conditional in the source; Section III.C, lines 334–341 and 455–456, assumes concavity of the uncertainty functional to extend the argument to mixed states. "
                        + "Here ℏ = 1 and the assertion ranges over finite mixtures of physical one-mode Gaussian densities. "
                        + "The weights are nonnegative and sum to one; a and c are positive, and each component determinant is at least 1/4. "
                        + "The two entropy integrands and the phase-space second-moment integrand must be integrable. "
                        + "There is no separate assumption n > 0: normalization rules out the empty mixture. "
                        + "This class is contained in the source's all-state class, so a failure in this class disproves that universal reading."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("entropy-power-covariance-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Two oppositely displaced coherent states violate the inequality"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a real displacement d, let gₘ be the normal density with mean m and variance 1/2. "
                            + "Consider the equal mixture of the Gaussian Wigner densities with means (d,d) and (−d,−d), each having a = c = 1/2 and b = 0. "
                            + "Each component factors as gᵤ(x)gᵥ(p) at its mean (u,v): substituting the covariance entries gives the normalization 1/π and exponent −(x−u)² − (p−v)².")),
                    Paragraph(Text(
                        "The Gaussian moment integrals are ∫x gₘ(x) dx = m and ∫x² gₘ(x) dx = m² + 1/2, and the centered second moment is 1/2; the first- and second-moment integrands are integrable. "
                            + "These follow from the Gaussian density moments and the variance of the Gaussian measure. "
                            + "Also ln gₘ(x) = −(ln π)/2 − (x−m)². Integrating this identity against gₘ gives an integrable entropy integrand and entropy (ln(πe))/2.")),
                    Paragraph(Text(
                        "For nonnegative real numbers A and B, monotonicity of the logarithm gives A(ln A − ln 2) ≤ A ln((A+B)/2), treating A = 0 separately. "
                            + "Adding the corresponding inequality with A and B interchanged bounds −((A+B)/2) ln((A+B)/2) above by −(A ln A + B ln B)/2 + ((A+B)/2) ln 2. "
                            + "For normalized nonnegative densities f and g with the three entropy integrands integrable, integrating yields h((f+g)/2) ≤ (h(f)+h(g))/2 + ln 2.")),
                    Paragraph(Text(
                        "To justify integrability for the equal mixture of g_d and g_−d, each Gaussian is continuous, nonnegative and at most one, as follows from its logarithm. "
                            + "Their average therefore lies between zero and one, and its product with its logarithm is measurable and nonpositive. "
                            + "The pointwise bound just proved dominates the absolute value of that product by an integrable combination of the two Gaussian entropy integrands and the average density. "
                            + "Thus both marginal entropy integrands are integrable.")),
                    Paragraph(Text(
                        "Integrating the factored components in either coordinate shows that both marginals are (g_d + g_−d)/2. "
                            + "More generally, integrating a product f(x)g(p) against the two-component phase-space mixture gives the average of the products of its one-dimensional component integrals. "
                            + "The product-integral identity also gives integrability whenever the four component integrands are integrable. "
                            + "Applying it to the constant, linear and squared coordinate functions gives zero means, covarianceXX = covariancePP = d² + 1/2, and covarianceXP = d². "
                            + "Adding the two integrable squared-coordinate terms verifies the required phase-space second-moment integrability.")),
                    Paragraph(Text(
                        "The binary entropy estimate and the Gaussian entropy formula now give h(W_x) + h(W_p) ≤ ln(πe) + 2 ln 2. "
                            + "At d = 6 the covariance ratio is ((36 + 1/2)²)/((36 + 1/2)² − 36²) = 5329/145. "
                            + "Since 16 < 5329/145, logarithm monotonicity and ln 16 = 4 ln 2 give 2 ln 2 < (ln(5329/145))/2.")),
                    Paragraph(Text(
                        "Assume the universal inequality. Set n = 2, take both weights to be 1/2, set μx = μp to the vector (6,−6), and take the constant covariance families a = c = 1/2 and b = 0. "
                            + "The weights normalize, and each component determinant equals 1/4. The finite sum is precisely the equal mixture above. "
                            + "Substitute its marginals, the verified integrability conditions and its covariance entries into the assumed inequality. "
                            + "It requires ln(πe) ≤ h(W_x) + h(W_p) − (ln(5329/145))/2, whereas the entropy upper bound and the strict logarithmic estimate make the right-hand side smaller than ln(πe). "
                            + "This contradiction proves the negation of the universal statement.")),
                    Paragraph(Text(
                        "The counterexample consists of mixed states with positive Wigner functions. "
                            + "The statement for pure states, the joint Wigner-entropy inequality, the extension to several modes and states with negative Wigner functions are outside this conclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hertz-jabbour-cerf-2017-covariance-corrected-entropy-power-uncertainty"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("entropy-power-covariance-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula GaussianWignerFormula()
    {
        Formula determinant = Subtract(Mul(X("a"), X("c")), Square(X("b")));
        Formula dx = Subtract(X("x"), X("μx"));
        Formula dp = Subtract(X("p"), X("μp"));
        Formula quadratic = Add(Subtract(Mul(X("c"), Square(dx)),
            Mul(Mul(Mul(D(2), X("b")), dx), dp)), Mul(X("a"), Square(dp)));
        Formula inverse = At(Qualified("Inv", "inv"),
            Mul(Mul(D(2), Qualified("Real", "pi")), At(Qualified("Real", "sqrt"), determinant)));
        Formula density = Mul(inverse, At(Qualified("Real", "exp"),
            Div(new Formula.Negate(Parenthesized(quadratic)), Mul(D(2), determinant))));
        return All("μx", Reals(), All("μp", Reals(), All("a", Reals(), All("b", Reals(),
            All("c", Reals(), All("x", Reals(), All("p", Reals(),
                Equal(LocalCall("gaussianWigner", X("μx"), X("μp"), X("a"), X("b"), X("c"), X("x"), X("p")), density))))))));
    }

    private static Formula MarginalFormula(bool position)
    {
        string coordinate = position ? "x" : "p";
        string integrated = position ? "p" : "x";
        return All("W", PhaseFunction(), All(coordinate, Reals(),
            Equal(LocalCall(position ? "marginalX" : "marginalP", X("W"), X(coordinate)),
                Integral(integrated, Reals(), At(X("W"), X("x"), X("p"))))));
    }

    private static Formula DensityEntropyFormula() => All("f", RealFunction(),
        Equal(LocalCall("densityEntropy", X("f")), new Formula.Negate(Parenthesized(
            Integral("x", Reals(), Mul(At(X("f"), X("x")), LogOf(At(X("f"), X("x")))))))));

    private static Formula MeanFormula(bool position) => All("W", PhaseFunction(),
        Equal(LocalCall(position ? "meanX" : "meanP", X("W")),
            Integral("r", PhaseSpace(), Mul(Coordinate(position ? (byte)1 : (byte)2), PhaseValue()))));

    private static Formula CovarianceFormula(string name, bool position, bool momentum)
    {
        Formula dx = Subtract(Coordinate(1), LocalCall("meanX", X("W")));
        Formula dp = Subtract(Coordinate(2), LocalCall("meanP", X("W")));
        Formula centered = position && momentum ? Mul(dx, dp) : Square(position ? dx : dp);
        return All("W", PhaseFunction(), Equal(LocalCall(name, X("W")),
            Integral("r", PhaseSpace(), Mul(centered, PhaseValue()))));
    }

    private static Formula ClaimProposition()
    {
        Formula component = LambdaOf("i", FinOf(X("n")), LambdaOf("y", Reals(),
            LocalCall("gaussianWigner", At(X("μx"), X("i")), At(X("μp"), X("i")),
                At(X("a"), X("i")), At(X("b"), X("i")), At(X("c"), X("i")), X("y"), X("p"))));
        Formula phaseDensity = LambdaOf("x", Reals(), LambdaOf("p", Reals(),
            At(Qualified("D5", "S3", "Entropy", "Mixing", "MixtureEntropyBracket", "mixture"),
                X("w"), Parenthesized(component), X("x"))));
        Formula xx = LocalCall("covarianceXX", X("W"));
        Formula pp = LocalCall("covariancePP", X("W"));
        Formula xp = LocalCall("covarianceXP", X("W"));
        Formula correction = Mul(Div(D(1), D(2)), LogOf(Div(Mul(xx, pp),
            Subtract(Mul(xx, pp), Square(xp)))));
        Formula conclusion = LE(LogOf(Mul(Qualified("Real", "pi"), At(Qualified("Real", "exp"), D(1)))),
            Subtract(Add(LocalCall("densityEntropy", LocalCall("marginalX", X("W"))),
                LocalCall("densityEntropy", LocalCall("marginalP", X("W")))), correction));
        Formula entropyX = LocalCall("marginalX", X("W"), X("x"));
        Formula entropyP = LocalCall("marginalP", X("W"), X("p"));
        Formula integrability = Imp(Integrable(LambdaOf("x", Reals(), Mul(entropyX, LogOf(entropyX)))),
            Imp(Integrable(LambdaOf("p", Reals(), Mul(entropyP, LogOf(entropyP)))),
                Imp(Integrable(LambdaOf("r", PhaseSpace(),
                    Mul(Add(Square(Coordinate(1)), Square(Coordinate(2))), PhaseValue()))), conclusion)));
        Formula densityBody = Seq(Qualified("let"), Sp, Typed(X("W"), PhaseFunction()), Sp, Colon, Eq, Sp,
            Parenthesized(phaseDensity), Semi, Sp, Parenthesized(integrability));
        Formula hypotheses = Imp(All("i", FinOf(X("n")), LE(D(0), At(X("w"), X("i")))),
            Imp(Equal(SumOver("i", FinOf(X("n")), At(X("w"), X("i"))), D(1)),
                Imp(All("i", FinOf(X("n")), LT(D(0), At(X("a"), X("i")))),
                    Imp(All("i", FinOf(X("n")), LT(D(0), At(X("c"), X("i")))),
                        Imp(All("i", FinOf(X("n")), LE(Div(D(1), D(4)),
                            Subtract(Mul(At(X("a"), X("i")), At(X("c"), X("i"))),
                                Square(At(X("b"), X("i")))))), densityBody)))));
        Formula family = Arrow(FinOf(X("n")), Reals());
        return All("n", Naturals(), All("w", family, All("μx", family, All("μp", family,
            All("a", family, All("b", family, All("c", family, hypotheses)))))));
    }

    private static Formula X(string name) => name switch
    {
        "μx" => Seq(Operatorname, Grp(Mu, Sp, F.Id("x"))),
        "μp" => Seq(Operatorname, Grp(Mu, Sp, F.Id("p"))),
        _ => F.Id(name),
    };
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements",
        "EntropyPowerCovarianceUncertaintyRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula PhaseSpace() => Seq(Reals(), Sp, Times, Sp, Reals());
    private static Formula RealFunction() => Arrow(Reals(), Reals());
    private static Formula PhaseFunction() => Arrow(Reals(), RealFunction());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Coordinate(byte index) => Seq(X("r"), Dot, D(index));
    private static Formula PhaseValue() => At(X("W"), Coordinate(1), Coordinate(2));
    private static Formula LogOf(Formula value) => At(Qualified("Real", "log"), Parenthesized(value));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), Typed(D(2), Naturals()));
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Mul(Formula left, Formula right) => Multiply(Parenthesized(left), Parenthesized(right));
    private static Formula Volume => Qualified("MeasureTheory", "MeasureSpace", "volume");
    private static Formula Integral(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(Int, Typed(X(name), type)), Sp, Parenthesized(body),
        Sp, Mathrm, Grp(F.Id("d")), Sp, Volume);
    private static Formula Integrable(Formula function) => At(Qualified("MeasureTheory", "Integrable"),
        Parenthesized(function), Volume);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(Parenthesized(hypothesis), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
