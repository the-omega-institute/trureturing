using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.Hermite;

internal sealed class PhysicalProductTotalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual physical product Hermite functions on Euclidean Lebesgue volume.",
        H("PhysicalProductTotality"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-hermite-function"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality.physicalHermite"),
                H("The actual physical product function"), StatementSource.FromAuthor(Disp(PhysicalFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/tauceti2026gaussianpolynomial")),
                Blocks(Paragraph(Text("The equation gives the actual function for arbitrary real parameters. Positivity is required by the totality theorem below."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("physical-product-totality"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality.physical_product_totality"),
                H("Every positive-parameter physical test family is total"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/tauceti2026gaussianpolynomial")),
                Blocks(
                Paragraph(Text("For every natural dimension d, E is EuclideanSpace Real (Fin d). ambientLebesgue is exactly "
                    + "the canonical volume measure on E; every MemLp and integral uses that same measure. hbar is positive "
                    + "and mass(j), frequency(j) are positive at every coordinate. The empty dimension is included.")),
                Paragraph(Text("physicalHermite is the displayed finite product. hermite is the probabilists Hermite polynomial, "
                    + "aeval evaluates it in Real, ofReal embeds each real factor into Complex, and pi is Real.pi. "
                    + "The coordinate length is sqrt(hbar/(mass(j)*frequency(j))). All square roots are nonnegative real roots. "
                    + "Thus every physical mode is real-valued inside Complex; its conjugate equals itself.")),
                Paragraph(Text("Finite-coordinate slot continuity extends actual physical test pairings from dense coordinate spans. "
                    + "Rectangle indicators, local pi-lambda induction and a common sigma-finite exhaustion then separate every actual "
                    + "Lebesgue L2 representative. The coordinate Gaussian-polynomial theorem is the canonical prerequisite.")),
                Paragraph(Text("The analytic constructions are attributed necessary-content adaptations from the fixed Tau Ceti revision "
                    + "listed in the Library note. They carry no research originality claim. No retained coordinate map, abstract basis, "
                    + "isometry, surjectivity, normalization or zero-dimension companion theorem is introduced.")),
                Paragraph(Text("This unit does not establish differential oscillator eigenaction, all-Schwartz restriction, maximal weak "
                    + "or coefficient graph, a finite Hermite operator core, tensor/operator domains, adapted symplectic or "
                    + "metaplectic transport, Gibbs positive trace/factorization, or normal-state second-moment covariance and uncertainty."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula alpha = Id("alpha"), g = Id("g"), x = Id("x");
        Formula modes = All([Bound("alpha", Indices())], Call("MemLp", Mode(alpha), D(2), Volume()));
        Formula vanishing = All([Bound("alpha", Indices())], Equal(Integral(Mul(Apply(Mode(alpha), x), Apply(g, x))), D(0)));
        Formula zero = Seq(g, Sp, Eq, Underscore, Grp(Operatorname, Grp(Id("ae")), Comma, Sp, Volume()), Sp, D(0));
        Formula separation = All([Bound("g", new Formula.TypeArrow(Space(), Complex()))],
            Imp(Call("MemLp", g, D(2), Volume()), Imp(vanishing, zero)));
        return Telescope(Imp(Positive(), And(modes, separation)));
    }

    private static Formula Id(string n) => F.Id(n);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(Id("C")));
    private static Formula Natural() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Fin() => Call("Fin", Id("d"));
    private static Formula Space() => Call("EuclideanSpace", Real(), Fin());
    private static Formula Indices() => new Formula.TypeArrow(Fin(), Natural());
    private static Formula Parameters() => new Formula.TypeArrow(Fin(), Real());
    private static Formula Volume() => new Formula.NamedConstant(FormulaIdentifier.Create("ambientLebesgue"));
    private static Formula Apply(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula.BoundVariable Bound(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula.BoundVariable[] v, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], b);
    private static Formula Telescope(Formula b) => All([Bound("d", Natural()), Bound("hbar", Real()), Bound("mass", Parameters()), Bound("frequency", Parameters())], b);
    private static Formula Positive() => And(Less(D(0), Id("hbar")), And(
        All([Bound("j", Fin())], Less(D(0), Apply(Id("mass"), Id("j")))),
        All([Bound("j", Fin())], Less(D(0), Apply(Id("frequency"), Id("j"))))));
    private static Formula Mode(Formula alpha) => Call("physicalHermite", Id("d"), Id("hbar"), Id("mass"), Id("frequency"), alpha);
    private static Formula Integral(Formula f) => Seq(Int, Underscore, Grp(Id("x"), Colon, Sp, Space()), Sp, f, Sp,
        Id("d"), Volume());
    private static Formula PhysicalFormula()
    {
        Formula j = Id("j"), alpha = Id("alpha"), x = Id("x");
        Formula ell = Call("sqrt", new Formula.Fraction(Id("hbar"), Mul(Apply(Id("mass"), j), Apply(Id("frequency"), j))));
        Formula scaled = new Formula.Fraction(Apply(x, j), ell);
        Formula hermite = Call("aeval", Mul(Call("sqrt", D(2)), scaled), Call("hermite", Apply(alpha, j)));
        Formula gaussian = Call("exp", new Formula.Negate(new Formula.Fraction(new Formula.Power(scaled, D(2)), D(2))));
        Formula normalization = Mul(Call("sqrt", ell), Call("sqrt", Mul(Call("factorial", Apply(alpha, j)),
            Call("sqrt", new Formula.NamedConstant(FormulaIdentifier.Create("pi"))))));
        Formula factor = Call("ofReal", new Formula.Fraction(Mul(hermite, gaussian), normalization));
        Formula product = Seq(new Formula.Subscript(F.Prod, Seq(j, Colon, Sp, Fin())), Grp(factor));
        return Telescope(All([Bound("alpha", Indices()), Bound("x", Space())], Equal(Apply(Mode(alpha), x), product)));
    }
}
