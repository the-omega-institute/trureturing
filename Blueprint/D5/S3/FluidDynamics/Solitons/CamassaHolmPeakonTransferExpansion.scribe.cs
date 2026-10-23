using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Solitons;

internal sealed class CamassaHolmPeakonTransferExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FluidDynamics/avan2026peakonquadratic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Camassa–Holm peakon transfer matrices have a partition expansion with explicit universal rational coefficients satisfying the values of Conjecture 5.2.",
        H("Universal coefficients for the peakon transfer expansion"),
        Blocks(
            Node("phase", "The hyperbolic phase", "phase", PhaseFormula(),
                "The positions are real and the parameter nu is complex. Their difference is cast to the complex numbers before multiplication by nu and division by two.",
                AssessedProvenance.FromRepo()),
            Node("a", "The antisymmetric hyperbolic matrix", "A", MatrixEntryFormula("A", "sinh"),
                "Equation (2.1) gives these entries with the factorized weights w_i w_j in place of the square root of p_i p_j. The weights may be complex; nonnegative momenta are recovered by taking w_i to be the real square root of p_i. Transposition is ordinary transposition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("t", "The symmetric hyperbolic matrix", "T", MatrixEntryFormula("T", "cosh"),
                "Equation (2.2) uses the same weights and phase with the complex hyperbolic cosine. Interchanging the two indices leaves the entry unchanged.",
                AssessedProvenance.FromLiterature(Source)),
            Node("s", "The position-sign matrix", "S", SignMatrixFormula(),
                "Equation (2.3) multiplies the corresponding entry of A by the sign of the real position difference, cast to the complex numbers. SignType.sign is zero at coincident positions, including the diagonal; no distinctness or ordering of the positions is assumed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("lambda", "The first spectral rational function", "Lambda", LambdaFormula(),
                "This rational function is the coefficient of T in the spectral matrix of §5.3. Its definition uses complex division for every gamma and z; the transfer expansion below excludes a zero denominator.",
                AssessedProvenance.FromLiterature(Source)),
            Node("xi", "The second spectral rational function", "xi", XiFormula(),
                "This rational function is the coefficient of A in §5.3. When 2z + gamma is nonzero, the two rational functions satisfy the conic relation xi squared = Lambda squared + gamma Lambda + 1 of (5.18).",
                AssessedProvenance.FromLiterature(Source)),
            Node("l", "The spectral Lax matrix", "L", LaxFormula(),
                "The decomposition in §5.3 is S + Lambda T + xi A, with complex scalar multiplication of matrices. The matrices are indexed by Fin N, and N may be zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("tau", "The transfer traces", "tau", TransferFormula(),
                "The transfer matrix in §5.3 is the trace of the m-th ordinary matrix power. This definition includes m = 0; the partition expansion is stated for positive m.",
                AssessedProvenance.FromLiterature(Source)),
            Node("h", "The Hamiltonian trace coefficients", "h", HamiltonianFormula(),
                "Equation (5.17) gives k times the trace of (T + (gamma/2) A)(S + A) to the power k−1. The factor k is cast to the complex numbers. The exponent uses natural subtraction, so it is zero at k = 0 as well as k = 1; the coefficient h at zero is zero because of the leading factor.",
                AssessedProvenance.FromLiterature(Source)),
            Node("coeff-family", "Rational families indexed by partitions", "CoeffFamily", CoefficientFamilyFormula(),
                "A coefficient family assigns a rational number to every natural m and every Nat.Partition m. It has no dependence on the number of positions, weights or spectral parameters.",
                AssessedProvenance.FromRepo()),
            Node("multiplicity-factor", "The factorials of repeated-part counts", "multiplicityFactor", MultiplicityFormula(),
                "For each distinct part, take the factorial of its multiplicity in the multiset of parts, then multiply these factorials. Passing to Multiset.toFinset ensures that each distinct part contributes exactly once.",
                AssessedProvenance.FromRepo()),
            Node("universal-coeff", "The universal rational coefficient", "universalCoeff", UniversalCoefficientFormula(),
                "For a partition with j parts, the coefficient is m (j−1)! divided by the product of its parts and the factorials of their multiplicities. All factors are cast from the natural numbers to the rational numbers before division; j−1 is natural subtraction. The definition also includes the empty partition of zero.",
                AssessedProvenance.FromRepo()),
            Node("part-monomial", "The product associated with a partition", "partMonomial", MonomialFormula(),
                "Map a complex-valued function over the multiset of parts and multiply the resulting multiset. Repeated parts therefore give repeated factors, and the empty multiset gives one.",
                AssessedProvenance.FromRepo()),
            Node("prescribed-values", "The three prescribed coefficient values", "prescribedValues", PrescribedFormula(),
                "The single-part coefficient is one for positive m, as in (5.20), and the coefficient of m parts equal to one is one, as in (5.21). For j < m−1, the partition consisting of m−j and j ones has coefficient m/(m−j). Both subtractions are in the natural numbers, and the denominator m−j is cast to the rational numbers after subtraction. The third clause needs no separate positivity hypothesis on m because its inequality already implies positivity.",
                AssessedProvenance.FromLiterature(Source)),
            Node("expansion", "The partition expansion of each transfer trace", "expansion", ExpansionFormula(),
                "Equation (5.20) is written as a single sum over Nat.Partition m. The number of parts gives the power of Lambda, and the part monomial is the product of the corresponding Hamiltonian coefficients. For positive m, all parts are positive and their sum is m. The identity holds for every finite N, complex weights and parameters, and real positions, provided 2z + gamma is nonzero; the rational coefficient is cast to the complex numbers.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The coefficient-existence proposition", "claim", ClaimFormula(),
                "Conjecture 5.2 asks for coefficients giving the transfer expansion and the prescribed values. This proposition also specifies the explicit family universalCoeff. The existential precedes every matrix and parameter quantifier in expansion, so a single rational family serves them all. Removing the equality to universalCoeff gives the source's existence assertion; uniqueness of coefficient families is not asserted.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("peakon-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The universal family gives the transfer expansion"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The matrix S + A has zero entries whenever the row position is at most the column position. Triangularity with blocks labelled by positions gives determinant one for its formal resolvent pencil, including coincident positions. The vectors with entries w_i exp(nu q_i/2) and w_i exp(−nu q_i/2) give the rank-two decomposition of T and A. The relation (5.18), together with the determinant identity for a rank-two perturbation and ordinary transposition, yields det(1 − tL) = 1 − Lambda sum over k ≥ 1 of (h_k/k)t^k as an identity of formal power series. Jacobi's formula gives the generating series of the transfer traces as the negative logarithmic derivative. Extracting each positive-degree coefficient and regrouping compositions by their multisets of parts gives m (j−1)! divided by the product of the parts and their multiplicity factorials. This family satisfies each of the three prescribed values and the expansion of Conjecture 5.2."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("avan-frappat-ragoucy-2026-peakon-transfer-expansion"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("peakon-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "FluidDynamics", "Solitons", "CamassaHolmPeakonTransferExpansion", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Rationals() => Seq(Mathbb, Grp(X("Q")));
    private static Formula FinOfN() => At(Qualified("Fin"), X("N"));
    private static Formula FunctionTo(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula PartitionOf(Formula m) => At(Qualified("Nat", "Partition"), m);
    private static Formula Parts() => At(Qualified("Nat", "Partition", "parts"), X("pi"));
    private static Formula PartCard() => At(Qualified("Multiset", "card"), Parts());
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula ScalarMultiply(Formula left, Formula right) =>
        At(Qualified("HSMul", "hSMul"), left, right);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);

    private static Formula MatrixParameters(Formula body) =>
        All("N", Naturals(), All("w", FunctionTo(FinOfN(), Complexes()),
            All("q", FunctionTo(FinOfN(), Reals()), All("nu", Complexes(), body))));
    private static Formula SpectralParameters(Formula body) =>
        MatrixParameters(All("gamma", Complexes(), All("z", Complexes(), body)));
    private static Formula MatrixCall(string name) => LocalCall(name, X("w"), X("q"), X("nu"));
    private static Formula SpectralCall(string name) =>
        LocalCall(name, X("w"), X("q"), X("nu"), X("gamma"), X("z"));
    private static Formula SpectralFunction(string name) => LocalCall(name, X("gamma"), X("z"));
    private static Formula Hamiltonians() => LocalCall("h", X("w"), X("q"), X("nu"), X("gamma"));
    private static Formula PartBinders(Formula body) => All("m", Naturals(), All("pi", PartitionOf(X("m")), body));

    private static Formula PhaseFormula()
    {
        Formula difference = Typed(Typed(Subtract(At(X("q"), X("i")), At(X("q"), X("j"))), Reals()), Complexes());
        return All("N", Naturals(), All("q", FunctionTo(FinOfN(), Reals()), All("nu", Complexes(),
            All("i", FinOfN(), All("j", FinOfN(),
                Equal(LocalCall("phase", X("q"), X("nu"), X("i"), X("j")),
                    Fraction(Multiply(X("nu"), difference), D(2))))))));
    }

    private static Formula MatrixEntryFormula(string name, string hyperbolic) => MatrixParameters(
        All("i", FinOfN(), All("j", FinOfN(),
            Equal(At(MatrixCall(name), X("i"), X("j")),
                Multiply(Multiply(At(X("w"), X("i")), At(X("w"), X("j"))),
                    At(Qualified("Complex", hyperbolic), LocalCall("phase", X("q"), X("nu"), X("i"), X("j"))))))));

    private static Formula SignMatrixFormula() => MatrixParameters(All("i", FinOfN(), All("j", FinOfN(),
        Equal(At(MatrixCall("S"), X("i"), X("j")),
            Multiply(Typed(At(Qualified("SignType", "sign"),
                Parenthesized(Subtract(At(X("q"), X("i")), At(X("q"), X("j"))))), Complexes()),
                At(MatrixCall("A"), X("i"), X("j")))))));

    private static Formula Denominator() => Add(Multiply(D(2), X("z")), X("gamma"));
    private static Formula LambdaFormula() => All("gamma", Complexes(), All("z", Complexes(),
        Equal(SpectralFunction("Lambda"), Fraction(Subtract(Power(X("z"), D(2)), D(1)), Denominator()))));
    private static Formula XiFormula() => All("gamma", Complexes(), All("z", Complexes(),
        Equal(SpectralFunction("xi"), Fraction(Add(Add(Power(X("z"), D(2)), Multiply(X("gamma"), X("z"))), D(1)), Denominator()))));

    private static Formula LaxFormula() => SpectralParameters(Equal(SpectralCall("L"),
        Add(Add(MatrixCall("S"), ScalarMultiply(SpectralFunction("Lambda"), MatrixCall("T"))),
            ScalarMultiply(SpectralFunction("xi"), MatrixCall("A")))));
    private static Formula TransferFormula() => SpectralParameters(All("m", Naturals(),
        Equal(At(SpectralCall("tau"), X("m")), At(Qualified("Matrix", "trace"), Power(SpectralCall("L"), X("m"))))));
    private static Formula HamiltonianFormula() => MatrixParameters(All("gamma", Complexes(), All("k", Naturals(),
        Equal(At(Hamiltonians(), X("k")), Multiply(Typed(X("k"), Complexes()),
            At(Qualified("Matrix", "trace"), Multiply(
                Parenthesized(Add(MatrixCall("T"), ScalarMultiply(Fraction(X("gamma"), D(2)), MatrixCall("A")))),
                Power(Add(MatrixCall("S"), MatrixCall("A")), Typed(Subtract(X("k"), D(1)), Naturals())))))))));

    private static Formula CoefficientFamilyFormula() => Equal(Local("CoeffFamily"),
        new Formula.TypeArrow(Typed(X("m"), Naturals()),
            new Formula.TypeArrow(PartitionOf(X("m")), Rationals())));
    private static Formula MultiplicityFormula()
    {
        Formula distinct = At(Qualified("Multiset", "toFinset"), Parts());
        Formula factorial = At(Qualified("Nat", "factorial"), At(Qualified("Multiset", "count"), X("r"), Parts()));
        Formula product = Seq(new Formula.Subscript(Prod,
            new Formula.Relation(X("r"), FormulaRelationOperator.MemberOf, distinct)), Sp, Parenthesized(factorial));
        return PartBinders(Equal(LocalCall("multiplicityFactor", X("pi")), product));
    }
    private static Formula UniversalCoefficientFormula() => PartBinders(
        Equal(LocalCall("universalCoeff", X("m"), X("pi")), Fraction(
            Multiply(Typed(X("m"), Rationals()),
                Typed(At(Qualified("Nat", "factorial"), Typed(Subtract(PartCard(), D(1)), Naturals())), Rationals())),
            Multiply(Typed(At(Qualified("Multiset", "prod"), Parts()), Rationals()),
                Typed(LocalCall("multiplicityFactor", X("pi")), Rationals())))));
    private static Formula MonomialFormula() => All("m", Naturals(),
        All("f", FunctionTo(Naturals(), Complexes()), All("pi", PartitionOf(X("m")),
            Equal(LocalCall("partMonomial", X("f"), X("pi")),
                At(Qualified("Multiset", "prod"), At(Qualified("Multiset", "map"), X("f"), Parts()))))));

    private static Formula PrescribedFormula()
    {
        Formula coefficient = At(X("a"), X("m"), X("pi"));
        Formula positive = Less(D(0), X("m"));
        Formula single = PartBinders(Implies(positive,
            Implies(Equal(Parts(), new Formula.SetLiteral([X("m")])), Equal(coefficient, D(1)))));
        Formula ones = PartBinders(Implies(positive,
            Implies(Equal(Parts(), At(Qualified("Multiset", "replicate"), X("m"), D(1))), Equal(coefficient, D(1)))));
        Formula remaining = Typed(Subtract(X("m"), X("j")), Naturals());
        Formula mixed = All("m", Naturals(), All("j", Naturals(), All("pi", PartitionOf(X("m")),
            Implies(Less(X("j"), Typed(Subtract(X("m"), D(1)), Naturals())),
                Implies(Equal(Parts(), At(Qualified("Multiset", "cons"), remaining,
                        At(Qualified("Multiset", "replicate"), X("j"), D(1)))),
                    Equal(coefficient, Fraction(Typed(X("m"), Rationals()), Typed(remaining, Rationals()))))))));
        return All("a", Local("CoeffFamily"), Iff(LocalCall("prescribedValues", X("a")), And(single, And(ones, mixed))));
    }

    private static Formula ExpansionFormula()
    {
        Formula summand = Multiply(Multiply(Power(SpectralFunction("Lambda"), PartCard()),
            Typed(At(X("a"), X("m"), X("pi")), Complexes())), LocalCall("partMonomial", Hamiltonians(), X("pi")));
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(X("pi"), PartitionOf(X("m")))), Sp, Parenthesized(summand));
        Formula body = All("N", Naturals(), All("m", Naturals(),
            All("w", FunctionTo(FinOfN(), Complexes()), All("q", FunctionTo(FinOfN(), Reals()),
                All("nu", Complexes(), All("gamma", Complexes(), All("z", Complexes(),
                    Implies(Less(D(0), X("m")), Implies(NotEqual(Denominator(), D(0)),
                        Equal(At(SpectralCall("tau"), X("m")), sum))))))))));
        return All("a", Local("CoeffFamily"), Iff(LocalCall("expansion", X("a")), body));
    }

    private static Formula ClaimFormula() => Iff(Local("claim"), Some("a", Local("CoeffFamily"),
        And(Equal(X("a"), Local("universalCoeff")),
            And(LocalCall("prescribedValues", X("a")), LocalCall("expansion", X("a"))))));
}
