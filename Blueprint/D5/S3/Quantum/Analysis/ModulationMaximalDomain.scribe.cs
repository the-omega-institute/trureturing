using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class ModulationMaximalDomainDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/teschl2009mathematical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive physical modulation has exactly the maximal coordinate multiplication domain in the actual L2 space.",
        H("Physical Modulation and Its Maximal Derivative Domain"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-modulation"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/ModulationMaximalDomain.physicalModulation"),
                H("Positive phase multiplication"),
                StatementSource.FromAuthor(Disp(DefinitionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural number d, E(d) is EuclideanSpace Real (Fin d), with Lebesgue measure volume, "
                    + "and H(d) is Lp Complex 2 volume. The brackets denote the almost-everywhere L2 class of the displayed function. "
                    + "The inner product is the real Euclidean inner product, cast to Complex where it multiplies a complex value. "
                    + "M(h,b,t,f) denotes physicalModulation h b t f. The formula defines M for every real h, using the total field convention 1/0=0; when h is zero the displayed phase is one. Its derivative theorem assumes h positive, so the fractions there use ordinary division."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("physical-modulation-has-deriv-at-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/ModulationMaximalDomain.physical_modulation_hasDerivAt_iff"),
                H("Complete strong derivative graph"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Here h is the positive Planck scalar hbar and i is Complex.I. Z(b,f) is the function x mapping to inner(b,x) times f(x). "
                        + "MemLp uses exponent two and volume. A witness u of MemLp(Z(b,f),2,volume) supplies toLp(u,Z(b,f)), namely u.toLp Z(b,f). "
                        + "The dot in the conclusion is complex scalar multiplication on H(d). HasDerivAt means the norm derivative with real time.")),
                    Paragraph(Text("The phase derivative bounds each difference quotient by the norm of (i/h) Z(b,f). "
                        + "When Z(b,f) is in L2, the squared error is dominated by four times the squared norm of that function. "
                        + "Dominated convergence therefore proves convergence of the actual L2 difference quotients and gives the derivative.")),
                    Paragraph(Text("Conversely, a strong derivative implies convergence of the quotient classes in L2 and hence in measure. "
                        + "A strictly increasing subsequence converges almost everywhere. Countably many representative equalities hold on a common set of full measure. "
                        + "Scalar derivative uniqueness identifies the limit with (i/h) Z(b,f). The derivative is in L2 and i/h is nonzero, so Z(b,f) is in L2.")),
                    Paragraph(Text("All finite dimensions, including zero, and all directions, including zero, are included. Both f and v are arbitrary actual L2 vectors. "
                        + "The derivative side requires no finite-volume, global L1, Schwartz, or coordinate-product integrability assumption. "
                        + "Changing a representative on a null set preserves both the condition and its toLp class.")),
                    Paragraph(Text("Teschl's maximal multiplication domain, equation (2.21), and the strong derivative characterization in Theorem 5.1(ii) give the literature correspondence. "
                        + "For the real multiplier A(x)=-inner(b,x)/h, the convention U(t)=exp(-itA) gives the positive phase and derivative (i/h) Z(b,f)."))),
                DescribeRole.Theorem))));

    private static Formula DefinitionFormula()
    {
        Formula d = F.Id("d"), h = F.Id("h"), b = F.Id("b"), t = F.Id("t"), f = F.Id("f"), x = F.Id("x");
        Formula phase = Call("exp", Quot(Mul(Mul(F.Id("i"), t), Call("inner", b, x)), h));
        Formula representative = Seq(OpenBracket, x, Colon, Sp, Call("E", d), Sp, Mapsto, Sp,
            Mul(phase, Apply(f, x)), CloseBracket);
        return All([Bound("d", Numbers("N")), Bound("h", Numbers("R")), Bound("b", Call("E", d)),
            Bound("t", Numbers("R")), Bound("f", Call("H", d))], Equal(Call("M", h, b, t, f), representative));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), h = F.Id("h"), b = F.Id("b"), f = F.Id("f"), v = F.Id("v"), t = F.Id("t"), u = F.Id("u");
        Formula z = Call("Z", b, f);
        Formula orbit = Seq(Open, t, Colon, Sp, Numbers("R"), Sp, Mapsto, Sp, Call("M", h, b, t, f), Close);
        Formula domain = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("u", Call("MemLp", z, D(2), new Formula.NamedConstant(FormulaIdentifier.Create("volume"))))],
            Equal(v, Seq(Quot(F.Id("i"), h), Sp, Cdot, Sp, Call("toLp", u, z))));
        Formula graph = new Formula.Logic(Call("HasDerivAt", orbit, v, D(0)), FormulaLogicOperator.Iff, domain);
        return All([Bound("d", Numbers("N")), Bound("h", Numbers("R")), Bound("b", Call("E", d)),
            Bound("f", Call("H", d)), Bound("v", Call("H", d))],
            new Formula.Logic(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, h),
                FormulaLogicOperator.Implies, Seq(Open, graph, Close)));
    }

    private static Formula Numbers(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Quot(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula.BoundVariable Bound(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, Formula value) => new Formula.Apply(function, [value]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
