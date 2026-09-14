using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class BaezDuarteNewtonMajorantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every-positive-epsilon decay of the actual coefficients yields a summable norm "
        + "majorant on each compact subset of the open critical half-plane.",
        H("Baez-Duarte Newton Compact Majorant"),
        Blocks(Describe.Lean(
            DescribeId.Create("compact-majorant"),
            DeclarationHandle.Create("D5/S3/Analytic/SeriesInequalities/"
                + "BaezDuarteNewtonMajorant.baez_duarte_newton_compact_majorant"),
            H("An all-index majorant for the actual Newton terms"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
            Blocks(
                Paragraph(Text("In the formula c denotes the imported actual baezDuarte sequence and P "
                    + "denotes normalizedPochhammer. The hypothesis is every-positive-epsilon eventual decay of the "
                    + "actual real baezDuarte coefficients, with a positive real constant and a "
                    + "natural threshold at least one. The conclusion supplies a nonnegative "
                    + "summable real sequence bounding every complex term c(k) P(k,s/2), "
                    + "for every index and every point of the compact set.")),
                Paragraph(Text("Compact separation gives a real lower bound a greater than one "
                    + "half. Choosing delta as (a minus one half) divided by four yields the "
                    + "common eventual exponent minus one minus delta. The producer's exact "
                    + "disk bound supplies the tail estimate. A finite-support correction from "
                    + "compact continuity bounds covers the whole prefix, including index zero. "
                    + "Compact separation and boundedness also apply to the empty compact set.")),
                Paragraph(Text("This is a repo-derived refinement of the source's compact "
                    + "convergence argument. The source proposition additionally identifies "
                    + "reciprocal zeta, which is not asserted here. The every-epsilon premise "
                    + "is retained as a hypothesis; neither RH direction is claimed. No "
                    + "nonpole, nonvanishing or real-only restriction is added. Utility kind "
                    + "none records a general analytic construction, not a finite computation."))),
            DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(FormulaDsl.Id(name), [.. args]);
    private static Formula NumberType(string name) => Seq(Mathbb, Grp(FormulaDsl.Id(name)));
    private static Formula Bind(FormulaQuantifier q, string x, Formula type, Formula body) =>
        Seq(Open, new Formula.Bind(q, FormulaIdentifier.Create(x), type, body), Close);
    private static Formula All(string x, Formula type, Formula body) => Bind(FormulaQuantifier.ForAll, x, type, body);
    private static Formula Some(string x, Formula type, Formula body) => Bind(FormulaQuantifier.Exists, x, type, body);
    private static Formula Statement()
    {
        Formula real = NumberType("R"), complex = NumberType("C"), nat = NumberType("N");
        Formula k = FormulaDsl.Id("k"), s = FormulaDsl.Id("s"), c = FormulaDsl.Id("C"), n = FormulaDsl.Id("N"), e = FormulaDsl.Id("e");
        Formula set = FormulaDsl.Id("K"), g = FormulaDsl.Id("g");
        Formula tail = All("k", nat, Seq(n, Le, Sp, k, Rightarrow, Sp,
            new Formula.Absolute(Call("c", k)), Le, Sp, c, Sp,
            new Formula.Power(k, Seq(Minus, new Formula.Fraction(D(3), D(4)), Plus, e))));
        Formula threshold = Some("N", nat, Seq(D(1), Le, Sp, n, Land, Sp, tail));
        Formula constant = Some("C", real, Seq(D(0), Lt, c, Land, Sp, threshold));
        Formula decay = All("e", real, Seq(D(0), Lt, e, Rightarrow, Sp, constant));
        Formula half = All("s", complex, Seq(s, InMacro, Sp, set, Rightarrow, Sp,
            new Formula.Fraction(D(1), D(2)), Lt, Call("Re", s)));
        Formula conclusion = Some("g", new Formula.TypeArrow(nat, real),
            Seq(Call("Summable", g), Land, Sp,
                All("k", nat, Seq(D(0), Le, Sp, new Formula.Apply(g, [k]))), Land, Sp,
                All("k", nat, All("s", complex, Seq(s, InMacro, Sp, set, Rightarrow, Sp,
                    new Formula.Norm(Seq(Call("c", k), Sp,
                        Call("P", k, new Formula.Fraction(s, D(2))))),
                    Le, Sp, new Formula.Apply(g, [k]))))));
        return Disp(Seq(decay, Rightarrow, Sp,
            All("K", Call("Set", complex), Seq(Call("IsCompact", set), Land, Sp, half,
                Rightarrow, Sp, conclusion))));
    }
}
