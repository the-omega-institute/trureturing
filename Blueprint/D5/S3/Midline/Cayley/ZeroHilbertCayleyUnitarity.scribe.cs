using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class ZeroHilbertCayleyUnitarityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Midline/Cayley/ZeroHilbertCayleyUnitarity."
            + "cayley_unitarity_defect_formula_on_zero_hilbert_space";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Cayley multiplier on the multiplicity-expanded zero Hilbert space has the exact "
            + "star-unitarity defect, and its vanishing is equivalent to the Riemann hypothesis.",
        H("Zero-Hilbert Cayley Unitarity"),
        Blocks(Describe.Lean(
            DescribeId.Create("cayley-unitarity-on-the-zero-hilbert-space"),
            DeclarationHandle.Create(Declaration),
            H("The Cayley defect and all of its unitarity characterizations"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let I_Z be the dependent sum of Fin(multiplicity(n)) over the distinct "
                        + "zeros stored by Z, and let H_Z be ell squared on I_Z. The vector e_v "
                        + "is the canonical single-coordinate vector. The coefficient c_v is "
                        + "(Z.zero(v.1) - 1) / Z.zero(v.1), and C_Z is the repository's bounded "
                        + "diagonal operator built from the full coefficient family.")),
                Paragraph(Text(
                    "The exhaustiveness binder states that Z covers every zeta zero in the "
                        + "domain quantified by Mathlib's RiemannHypothesis. This is the public "
                        + "bridge from the source's multiset of all nontrivial zeros to ZeroData, "
                        + "whose native exhaustive field covers zeros in the open strip.")),
                Paragraph(Text(
                    "For every multiplicity coordinate, the statement gives the diagonal action, "
                        + "the basis-vector star defect, both scalar formulas for the defect, and "
                        + "the two pointwise norm characterizations. It then identifies the "
                        + "Riemann hypothesis with coefficient norm one, the Gram identity, and "
                        + "standard unitary membership, and directly relates the latter to norm "
                        + "preservation on every canonical basis vector.")),
                Paragraph(Text(
                    "Boundedness follows from continuity and nonvanishing of zeta near zero, "
                        + "which gives a uniform lower bound for the norms of all supplied zeros. "
                        + "The result is conditional on supplied ZeroData and its explicit "
                        + "exhaustiveness bridge; it does not construct either object or prove "
                        + "the Riemann hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Midline/Cayley/CayleyUnitarityDefect")),
            DocumentEdge.Dependency.Create(
                GidRef.Create(
                    "D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaBridge/RhLocatesZeroData")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Iff, Sp, Open, right, Close);

    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, Open, conclusion, Close);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = Seq(Open, result, Close, Sp, Land, Sp, Open, clauses[index], Close);
        }

        return result;
    }

    private static Formula ForallIn(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);

    private static Formula ExistsIn(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula z = F.Id("Z");
        Formula h = F.Id("h");
        Formula rho = Rho;
        Formula n = F.Id("n");
        Formula v = F.Id("v");
        Formula zero = D(0);
        Formula one = D(1);
        Formula two = D(2);
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula half = new Formula.Fraction(one, two);
        Formula coordinate = Call("ZeroCoordinate", z);
        Formula index = Call("fst", v);
        Formula zeroAtIndex = Call("zero", z, index);
        Formula zeroAtN = Call("zero", z, n);
        Formula coefficient = Call("cayleyCoefficient", zeroAtIndex);
        Formula defect = new Formula.Subscript(DeltaLower, v);
        Formula cayley = Call("zeroCayleyOperator", z);
        Formula basis = Call("single", two, v, one);
        Formula adjoint = Seq(cayley, Caret, Grp(Star));
        Formula gram = Seq(adjoint, cayley);
        Formula identity = F.Id("I");
        Formula re = Seq(Re, Open, zeroAtIndex, Close);
        Formula coefficientNorm = new Formula.Norm(coefficient);
        Formula basisNorm = new Formula.Norm(basis);
        Formula imageNorm = new Formula.Norm(Apply(cayley, basis));
        Formula rh = Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));
        Formula unitary = Call("Unitary", cayley);

        Formula trivialZero = Seq(Minus, two, Open, n, Plus, one, Close);
        Formula noTrivialZero = Seq(
            Neg, Sp, ExistsIn(n, natural, Equal(rho, trivialZero)));
        Formula exhaustivePremise = ForallIn(
            rho,
            complex,
            ImpliesFormula(
                And(
                    Equal(Call("riemannZeta", rho), zero),
                    noTrivialZero,
                    NotEqual(rho, one)),
                ExistsIn(n, natural, Equal(zeroAtN, rho))));

        Formula action = Equal(
            Apply(cayley, basis),
            Seq(coefficient, Cdot, basis));
        Formula defectAction = Equal(
            Apply(Seq(Open, gram, Minus, identity, Close), basis),
            Seq(defect, Cdot, basis));
        Formula defectDefinition = Equal(
            defect,
            Seq(new Formula.Power(coefficientNorm, two), Minus, one));
        Formula defectPosition = Equal(
            defect,
            new Formula.Fraction(
                Seq(one, Minus, two, re),
                new Formula.Power(new Formula.Norm(zeroAtIndex), two)));
        Formula coefficientMidline = IffFormula(
            Equal(coefficientNorm, one),
            Equal(re, half));
        Formula basisMidline = IffFormula(
            Equal(re, half),
            Equal(imageNorm, basisNorm));
        Formula pointwise = ForallIn(
            v,
            coordinate,
            Seq(
                Operatorname, Grp(F.Id("let")), Sp, defectDefinition, Semi,
                RowBreak, Grp(),
                And(
                    action,
                    defectAction,
                    defectPosition,
                    coefficientMidline,
                    basisMidline)));

        Formula allCoefficients = ForallIn(
            v,
            coordinate,
            Equal(coefficientNorm, one));
        Formula gramIdentity = Equal(gram, identity);
        Formula allBasisNorms = ForallIn(
            v,
            coordinate,
            Equal(imageNorm, basisNorm));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma,
            RowBreak, Grp(),
            Forall, Sp, h, Colon, Sp, Open, exhaustivePremise, Close, Comma,
            RowBreak, Grp(),
            Open, pointwise, Close, Sp, Land,
            RowBreak, Grp(), Open, IffFormula(rh, allCoefficients), Close, Sp, Land,
            RowBreak, Grp(), Open, IffFormula(rh, gramIdentity), Close, Sp, Land,
            RowBreak, Grp(), Open, IffFormula(rh, unitary), Close, Sp, Land,
            RowBreak, Grp(), Open, IffFormula(allBasisNorms, unitary), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
