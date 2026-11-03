using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class OnbTomographyHolevoRatioDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Estimation/dasetal2025holevo");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full orthonormal qudit tomography has NHCRB at most d+1 times HCRB.",
        H("The Holevo ratio for full orthonormal tomography"),
        Blocks(
            Definition("traceless-onb", "IsTracelessONB", "A traceless Hermitian orthonormal basis",
                BasisFormula(), AssessedProvenance.FromLiterature(Source),
                "The family b consists of d squared minus one traceless Hermitian matrices. "
                + "Their trace pairings are the Kronecker delta, with normalization one as in "
                + "Das et al., DraftQuantumSubmission.tex, lines 2072–2074. For d at least two, "
                + "adjoining the identity spans all complex d by d matrices."),
            Definition("model", "model", "The linear tomography model",
                ModelFormula(), AssessedProvenance.FromLiterature(Source),
                "The real coordinates theta multiply the basis matrices, and the identity has "
                + "coefficient one over d. For a traceless Hermitian orthonormal basis and d at "
                + "least two this matrix has trace one; positive semidefiniteness selects the "
                + "density matrices. This is the linear model of Section 5.2 of Das et al."),
            Definition("locally-unbiased", "IsLUB", "Locally unbiased operators",
                LubFormula(), AssessedProvenance.FromLiterature(Source),
                "Each x k is Hermitian. Its expectation in the model equals theta k, and its "
                + "trace pairing with b j equals the Kronecker delta. These are the uncentered "
                + "local unbiasedness constraints of Das et al., lines 596–602; the derivatives "
                + "of the linear model are precisely the matrices b j."),
            Definition("covariance", "zMatrix", "The uncentered covariance matrix",
                ZFormula(), AssessedProvenance.FromLiterature(Source),
                "For a d by d matrix rho and n operators x, the j,k entry is the trace of "
                + "rho times x j times x k, in that order. The parameter square has not been "
                + "subtracted. This is the matrix in Das et al., lines 658–664."),
            Definition("imaginary-part", "imPart", "The entrywise imaginary part",
                ImaginaryFormula(), AssessedProvenance.FromRepo(Source),
                "Take the imaginary part of each complex entry and embed the resulting real "
                + "number back into the complex numbers. Thus the trace norm can be applied "
                + "to a complex matrix representing the entrywise imaginary part."),
            Definition("admissible", "IsAdmissible", "Admissible Hermitian blocks",
                AdmissibleFormula(), AssessedProvenance.FromLiterature(Source),
                "The blocks l j k are Hermitian and symmetric in the parameter indices. "
                + "After flattening the parameter and quantum indices into pairs, the block "
                + "matrix with blocks l j k minus x j times x k is positive semidefinite. "
                + "These are the constraints in Das et al., lines 588–608."),
            Definition("hcrb", "hcrb", "The Holevo Cramer–Rao bound",
                HolevoFormula(), AssessedProvenance.FromLiterature(Source),
                "Take the infimum over all locally unbiased families of the real part of "
                + "the covariance trace plus the trace norm of its entrywise imaginary part, "
                + "then subtract the sum of squared real parameters. The weight is the "
                + "identity. This is the infimum form of Das et al., lines 658–666; the "
                + "trace norm is the trace of the positive square root of the conjugate "
                + "transpose product."),
            Definition("nhcrb", "nhcrb", "The Nagaoka–Hayashi Cramer–Rao bound",
                NagaokaFormula(), AssessedProvenance.FromLiterature(Source),
                "Take the infimum over both locally unbiased families x and admissible "
                + "block families l of the real part of the sum of the traces of rho times "
                + "l j j. Subtract the same parameter square. This is the identity weight "
                + "bound of Das et al., lines 588–608, with the double trace written as a "
                + "sum over diagonal blocks."),
            Definition("claim", "claim", "The proposed full tomography ratio bound",
                Equal(Local("claim"), Parenthesized(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                "Das et al. write, ‘we expect the attainable bound to be d+1’ and "
                + "‘Thus for the linear GMM model, we propose Rᴺᴴ[{rho_theta}] ≤ d+1’ "
                + "(DraftQuantumSubmission.tex, lines 1147–1155). The formal claim covers "
                + "every orthonormal traceless Hermitian basis, including the source's "
                + "generalized Gell-Mann matrices: for every d at least two and every "
                + "positive semidefinite model matrix, NHCRB is at most d+1 times HCRB."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The ratio bound for every orthonormal basis"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Put rho = model d b theta and P = Re tr(rho squared). First, "
                        + "adjoin the identity to b. The trace pairings give a dual family, "
                        + "so linear independence and the dimension count give the expansion "
                        + "A = (tr A/d) I + sum_j tr(b j A) b j for every complex matrix A. "
                        + "For a locally unbiased x, the expectation equation forces tr(x k) "
                        + "to vanish, and the remaining pairings then force x k = b k. "
                        + "Conversely b itself is locally unbiased. Hence the Holevo "
                        + "infimum has just one cost value.")),
                    Paragraph(Text(
                        "Applying the expansion to matrix units gives the contraction "
                        + "sum_j b j A b j = tr(A) I − A/d. At A = I this is the Casimir "
                        + "identity sum_j (b j) squared = ((d squared − 1)/d) I. "
                        + "Consequently Re tr(Z) = (d squared − 1)/d, while orthonormality "
                        + "gives P = 1/d + sum_j (theta j) squared. After subtracting the "
                        + "parameter square the real contribution is d − P.")),
                    Paragraph(Text(
                        "For the imaginary contribution let Z = zMatrix rho b and "
                        + "A = i imPart Z = (Z − transpose Z)/2. Hermitian symmetry and "
                        + "cyclicity of trace make Z Hermitian; its quadratic forms are "
                        + "nonnegative trace pairings with rho, so Z is positive semidefinite. "
                        + "Trace one also gives I − rho positive "
                        + "semidefinite, so its covariance is I − Z and is positive "
                        + "semidefinite. Adding these matrices and their transposes shows "
                        + "I + 2A and I − 2A are positive semidefinite. The matrix A is "
                        + "Hermitian, and every eigenvalue therefore has absolute value at "
                        + "most one half. Thus its trace norm is at least twice Re tr(A squared). "
                        + "For the commutators c j = rho b j − b j rho, the trace pairing "
                        + "expansion gives sum_k tr(c j b k) squared = tr((c j) squared), "
                        + "and the contraction identity gives sum_j tr((c j) squared) "
                        + "= 2 − 2d tr(rho squared). The entries of A are tr(c j b k)/2 "
                        + "and satisfy A k j = −A j k. These identities give "
                        + "Re tr(A squared) = (dP − 1)/2. "
                        + "Multiplication by i preserves trace norm, proving "
                        + "traceNorm(imPart Z) ≥ dP − 1.")),
                    Paragraph(Text(
                        "The unique locally unbiased family reduces HCRB to the real "
                        + "contribution plus this trace norm. Hence HCRB ≥ d − P + dP − 1 "
                        + "= (d − 1)(1 + P). Since P = 1/d plus a sum of squares, this "
                        + "implies HCRB ≥ (d squared − 1)/d.")),
                    Paragraph(Text(
                        "For NHCRB use the source's feasible blocks L* j k = "
                        + "((d + 1)/(d + 2)) (b j b k + b k b j + delta j k I) "
                        + "(Das et al., lines 2592–2616). To check the semidefinite "
                        + "constraint, set r = 1/(d + 1) and form the block matrix T with "
                        + "blocks b k b j − r b j b k. The contraction and Casimir "
                        + "identities give T squared = I; T is Hermitian. Its flattened "
                        + "matrix S is a Hermitian involution, so I + S is positive "
                        + "semidefinite. The matrix with blocks L* j k − b j b k equals "
                        + "((d + 1)/(d + 2)) (I + S), a nonnegative multiple of that "
                        + "matrix. The blocks are also symmetric and Hermitian.")),
                    Paragraph(Text(
                        "Summing the diagonal feasible blocks and using the Casimir "
                        + "identity and tr(rho) = 1 gives cost "
                        + "((d squared − 1)(d + 1))/d. Every admissible cost is nonnegative: "
                        + "the diagonal block l j j − (x j) squared is positive "
                        + "semidefinite, and (x j) squared is positive semidefinite because "
                        + "x j is Hermitian. Their sum l j j is therefore positive semidefinite, "
                        + "and the trace pairing with rho is nonnegative. Thus the infimum "
                        + "is bounded below and is at most the feasible cost. After "
                        + "subtracting the parameter square, NHCRB ≤ "
                        + "((d squared − 1)(d + 1))/d − sum_j (theta j) squared.")),
                    Paragraph(Text(
                        "Finally discard the nonnegative parameter square from this "
                        + "upper bound, factor out d + 1, and multiply the Holevo lower "
                        + "bound by the nonnegative number d + 1. This yields "
                        + "NHCRB ≤ (d + 1)((d squared − 1)/d) ≤ (d + 1) HCRB."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("das-et-al-2025-onb-tomography-holevo-ratio"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula BasisFormula() => OverModelBasis(Equivalence(
        LocalCall("IsTracelessONB", X("d"), X("b")),
        And(All("j", ParameterIndex(), Hermitian(At(X("b"), X("j")))),
            And(All("j", ParameterIndex(), Equal(Trace(At(X("b"), X("j"))), Typed(D(0), Complexes()))),
                All("j", ParameterIndex(), All("k", ParameterIndex(),
                    Equal(Trace(Mul(At(X("b"), X("j")), At(X("b"), X("k")))),
                        DeltaValue(Complexes()))))))));

    private static Formula ModelFormula() => OverModel(Equal(
        Typed(Model(), QuantumMatrix()),
        PlusOf(Smul(Div(Typed(D(1), Complexes()), Cast(X("d"), Complexes())),
                Typed(D(1), QuantumMatrix())),
            SumOver("j", ParameterIndex(), Smul(OfReal(At(X("θ"), X("j"))), At(X("b"), X("j")))))));

    private static Formula LubFormula() => OverModel(All("x", BasisType(), Equivalence(
        LocalCall("IsLUB", X("d"), X("b"), X("θ"), X("x")),
        And(All("k", ParameterIndex(), Hermitian(At(X("x"), X("k")))),
            And(All("k", ParameterIndex(), Equal(Trace(Mul(Model(), At(X("x"), X("k")))),
                    OfReal(At(X("θ"), X("k"))))),
                All("j", ParameterIndex(), All("k", ParameterIndex(),
                    Equal(Trace(Mul(At(X("b"), X("j")), At(X("x"), X("k")))),
                        DeltaValue(Complexes())))))))));

    private static Formula ZFormula() => All("d", Naturals(), All("n", Naturals(),
        All("ρ", QuantumMatrix(), All("x", OperatorFamily(), Equal(
            Typed(LocalCall("zMatrix", X("ρ"), X("x")), ParameterMatrix()),
            LambdaOf("j", FinOf(X("n")), LambdaOf("k", FinOf(X("n")),
                Trace(Mul(Mul(X("ρ"), At(X("x"), X("j"))), At(X("x"), X("k")))))))))));

    private static Formula ImaginaryFormula() => All("n", Naturals(), All("a", ParameterMatrix(), Equal(
        Typed(LocalCall("imPart", X("a")), ParameterMatrix()),
        LambdaOf("j", FinOf(X("n")), LambdaOf("k", FinOf(X("n")),
            OfReal(At(Qualified("Complex", "im"), At(X("a"), X("j"), X("k")))))))));

    private static Formula AdmissibleFormula()
    {
        Formula pairType = Seq(FinOf(X("n")), Sp, Times, Sp, FinOf(X("d")));
        Formula aj = At(Qualified("Prod", "fst"), X("a"));
        Formula bk = At(Qualified("Prod", "fst"), X("b"));
        Formula ai = At(Qualified("Prod", "snd"), X("a"));
        Formula bi = At(Qualified("Prod", "snd"), X("b"));
        Formula block = LambdaOf("a", pairType, LambdaOf("b", pairType,
            At(Parenthesized(Sub(At(X("l"), aj, bk), Mul(At(X("x"), aj), At(X("x"), bk)))), ai, bi)));
        return All("d", Naturals(), All("n", Naturals(), All("x", OperatorFamily(),
            All("l", BlockFamily(), Equivalence(LocalCall("IsAdmissible", X("x"), X("l")),
                And(All("j", FinOf(X("n")), All("k", FinOf(X("n")), Hermitian(At(X("l"), X("j"), X("k"))))),
                    And(All("j", FinOf(X("n")), All("k", FinOf(X("n")),
                            Equal(At(X("l"), X("j"), X("k")), At(X("l"), X("k"), X("j"))))),
                        Positive(Typed(block, MatrixOf(pairType, pairType))))))))));
    }

    private static Formula HolevoFormula()
    {
        Formula z = LocalCall("zMatrix", Model(), X("x"));
        Formula cost = PlusOf(RealPart(Trace(z)), NormOfImaginary(z));
        Formula costs = SetOf("c", Reals(), Some("x", BasisType(), And(
            LocalCall("IsLUB", X("d"), X("b"), X("θ"), X("x")), Equal(X("c"), cost))));
        return OverModel(Equal(Typed(LocalCall("hcrb", X("d"), X("b"), X("θ")), Reals()),
            Sub(At(Qualified("sInf"), costs), ParameterSquare())));
    }

    private static Formula NagaokaFormula()
    {
        Formula blocks = Arrow(ParameterIndex(), Arrow(ParameterIndex(), QuantumMatrix()));
        Formula cost = RealPart(SumOver("j", ParameterIndex(), Trace(Mul(Model(), At(X("l"), X("j"), X("j"))))));
        Formula costs = SetOf("c", Reals(), Some("x", BasisType(), Some("l", blocks, And(
            LocalCall("IsLUB", X("d"), X("b"), X("θ"), X("x")),
            And(LocalCall("IsAdmissible", X("x"), X("l")), Equal(X("c"), cost))))));
        return OverModel(Equal(Typed(LocalCall("nhcrb", X("d"), X("b"), X("θ")), Reals()),
            Sub(At(Qualified("sInf"), costs), ParameterSquare())));
    }

    private static Formula ClaimFormula() => All("d", Naturals(), Implies(LE(D(2), X("d")),
        All("b", BasisType(), Implies(LocalCall("IsTracelessONB", X("d"), X("b")),
            All("θ", Arrow(ParameterIndex(), Reals()), Implies(Positive(Model()),
                LE(LocalCall("nhcrb", X("d"), X("b"), X("θ")),
                    Mul(PlusOf(Cast(X("d"), Reals()), Typed(D(1), Reals())),
                        LocalCall("hcrb", X("d"), X("b"), X("θ"))))))))));

    private static Formula OverModelBasis(Formula body) => All("d", Naturals(), All("b", BasisType(), body));
    private static Formula OverModel(Formula body) => OverModelBasis(All("θ", Arrow(ParameterIndex(), Reals()), body));
    private static Formula Model() => LocalCall("model", X("d"), X("b"), X("θ"));
    private static Formula ParameterIndex() => FinOf(Sub(new Formula.Power(X("d"), D(2)), D(1)));
    private static Formula QuantumMatrix() => MatrixOf(FinOf(X("d")), FinOf(X("d")));
    private static Formula ParameterMatrix() => MatrixOf(FinOf(X("n")), FinOf(X("n")));
    private static Formula BasisType() => Arrow(ParameterIndex(), QuantumMatrix());
    private static Formula OperatorFamily() => Arrow(FinOf(X("n")), QuantumMatrix());
    private static Formula BlockFamily() => Arrow(FinOf(X("n")), Arrow(FinOf(X("n")), QuantumMatrix()));
    private static Formula ParameterSquare() => SumOver("j", ParameterIndex(), new Formula.Power(At(X("θ"), X("j")), D(2)));
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula RealPart(Formula value) => At(Qualified("Complex", "re"), value);
    private static Formula NormOfImaginary(Formula value) => At(
        Qualified("D5", "S3", "Quantum", "Foundation", "FiniteTraceDistance", "traceNorm"), LocalCall("imPart", value));
    private static Formula Hermitian(Formula value) => At(Qualified("Matrix", "IsHermitian"), value);
    private static Formula Positive(Formula value) => At(Qualified("Matrix", "PosSemidef"), value);
    private static Formula DeltaValue(Formula type) => At(Qualified("ite"), Equal(X("j"), X("k")), Typed(D(1), type), Typed(D(0), type));
    private static Formula OfReal(Formula value) => Typed(At(Qualified("Complex", "ofReal"), value), Complexes());
    private static Formula Cast(Formula value, Formula type) => Typed(At(Qualified("Nat", "cast"), value), type);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements", "OnbTomographyHolevoRatio", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch { "θ" => Theta, "ρ" => Rho, _ => F.Id(name) };
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
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula MatrixOf(Formula rows, Formula columns) => At(Qualified("Matrix"), rows, columns, Complexes());
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, X(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Smul(Formula scalar, Formula vector) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula PlusOf(Formula left, Formula right) => Add(Parenthesized(left), Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) => Subtract(Parenthesized(left), Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => Multiply(Parenthesized(left), Parenthesized(right));
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
}
