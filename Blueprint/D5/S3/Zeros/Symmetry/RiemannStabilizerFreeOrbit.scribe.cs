using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class RiemannStabilizerFreeOrbitDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/Symmetry/RiemannStabilizerFreeOrbit."
            + "riemann_stabilizer_free_orbit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-line localization fixes every nontrivial zero under conjugate reflection, "
            + "while a nonreal off-line zero retains a free four-point symmetry orbit.",
        H("Riemann Stabilizers and Free Zero Orbits"),
        Blocks(Describe.Lean(
            DescribeId.Create("riemann-stabilizer-growth-and-free-zero-orbits"),
            DeclarationHandle.Create(Declaration),
            H("Localization enlarges stabilizers without restoring symmetry"),
            StatementSource.FromAuthor(OrbitFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first public conjunct applies the pinned Riemann-hypothesis location "
                        + "theorem to every classical nontrivial zero and identifies the source's "
                        + "J action with conjugate reflection.")),
                Paragraph(Text(
                    "The second public conjunct constructs the source's literal Klein orbit "
                        + "from conjugation, functional reflection, and conjugate reflection. "
                        + "The pinned zeta covariance and reflection theorems keep every orbit "
                        + "member inside the nontrivial zero set, and the two generators preserve "
                        + "the orbit as a set.")),
                Paragraph(Text(
                    "Nonzero imaginary part and displacement from one half make the four orbit "
                        + "members pairwise distinct. No converse from a free orbit to the "
                        + "negation of the Riemann hypothesis and no real-axis nonvanishing "
                        + "statement is asserted."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Symmetry/ZetaConjugationCovariance")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = Seq(Open, result, Close, Sp, Land, Sp, Open, clauses[index], Close);
        }

        return result;
    }

    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, Open, conclusion, Close);

    private static Formula Member(Formula element, Formula collection) =>
        Seq(element, Sp, InMacro, Sp, collection);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula OrbitFormula()
    {
        Formula rho = Rho;
        Formula z = F.Id("z");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula zero = D(0);
        Formula one = D(1);
        Formula half = new Formula.Fraction(one, D(2));
        Formula rHypothesis = Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));
        Formula isZero(Formula value) => Call("IsNontrivialZero", value);
        Formula conjugate(Formula value) => Call("conj", value);
        Formula reflection(Formula value) => Seq(one, Minus, value);
        Formula mirror(Formula value) => Call("reflect", value);
        Formula orbit = Call("orbit", rho);
        Formula orbitLiteral = new Formula.SetLiteral(
            [rho, conjugate(rho), reflection(rho), mirror(rho)]);

        Formula fixedByMirror = Seq(
            Forall, Sp, rho, InMacro, Sp, complex, Comma, Sp,
            ImpliesFormula(isZero(rho), Equal(mirror(rho), rho)));
        Formula rhClause = ImpliesFormula(rHypothesis, fixedByMirror);

        Formula zeroClosure = Seq(
            Forall, Sp, z, InMacro, Sp, complex, Comma, Sp,
            ImpliesFormula(Member(z, orbit), isZero(z)));
        Formula reflectionClosure = Seq(
            Forall, Sp, z, InMacro, Sp, complex, Comma, Sp,
            Open, Member(z, orbit), Sp, Leftrightarrow, Sp,
            Member(reflection(z), orbit), Close);
        Formula conjugationClosure = Seq(
            Forall, Sp, z, InMacro, Sp, complex, Comma, Sp,
            Open, Member(z, orbit), Sp, Leftrightarrow, Sp,
            Member(conjugate(z), orbit), Close);
        Formula freeOrbit = ImpliesFormula(
            NotEqual(Seq(Operatorname, Grp(F.Id("Im")), Open, rho, Close), zero),
            ImpliesFormula(
                NotEqual(Seq(Re, Open, rho, Close), half),
                Equal(Call("card", orbit), D(4))));
        Formula orbitClause = Seq(
            Forall, Sp, rho, InMacro, Sp, complex, Comma, Sp,
            ImpliesFormula(
                isZero(rho),
                Seq(
                    Operatorname, Grp(F.Id("let")), Sp,
                    orbit, Colon, Sp, Eq, Sp, orbitLiteral, Semi,
                    RowBreak, Grp(),
                    And(zeroClosure, reflectionClosure, conjugationClosure, freeOrbit))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            rhClause, Sp, Land,
            RowBreak, Grp(), orbitClause, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
