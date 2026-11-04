using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class EfronSteinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance of a bounded measurable observable on a finite dependent product is bounded by half its total coordinate resampling energy.",
        H("Efron–Stein inequality on finite probability products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("efron-stein-pi"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/EfronStein.efronStein_pi"),
                H("Finite-product variance tensorization"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/armstrong2026efronstein")),
                Blocks(
                    Paragraph(Text("The index type is any finite type, including the empty type. Each coordinate has its own arbitrary measurable space and probability measure. The observable is a measurable real function on their dependent product with a single pointwise absolute bound M. The outer sample x follows the full product law, and the replacement y follows the probability measure of coordinate i. The coefficient is one half.")),
                    Paragraph(Text("Splitting off one coordinate gives the two-factor variance decomposition. The two-point variance identity supplies that coordinate’s resampling term; Jensen’s inequality bounds each resampling term of the conditional mean by the corresponding term of the original observable. Induction on the number of coordinates and a measure-preserving reindexing give the stated finite-product inequality. The empty product has zero variance and an empty energy sum.")),
                    Paragraph(Text("This is a credited port of Scott N. Armstrong’s CoarseGraining sources TwoPoint.lean, ProdDecomp.lean and Fin.lean at revision 310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be. The original Apache-2.0 copyright and full license are retained, with source correspondence in the literature note. The source proof is consolidated and adapted to the receiving Mathlib API.")),
                    Paragraph(Text("Coordinates may differ and their measures need not be identical. No topology, Borel-space condition, symmetry or nondegeneracy is required. The conclusion concerns bounded observables and finite products; it supplies variance control from coordinate sensitivities."))),
                DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula D(int n) => new Formula.Number(n);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string n, Formula type) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Product => Seq(All("i", V("I")), App(V("Omega"), V("i")));
    private static Formula PiMeasure => Call("MeasurePi", V("mu"));
    private static Formula Integral(string n, Formula measure, Formula body) =>
        Seq(new Formula.Subscript(Int, V(n)), Sp, body, Sp, Call("d", measure), Open, V(n), Close);
    private static Formula Statement()
    {
        var difference = Subtract(App(V("F"), Call("update", V("x"), V("i"), V("y"))),
            App(V("F"), V("x")));
        var energy = Integral("x", PiMeasure,
            Integral("y", App(V("mu"), V("i")), new Formula.Power(Parenthesized(difference), D(2))));
        return Disp(new Formula.Aligned([
            Seq(All("I", Call("Type")), Instance(Call("Fintype", V("I"))),
                Instance(Call("DecidableEq", V("I"))),
                All("Omega", new Formula.TypeArrow(V("I"), Call("Type"))),
                Instance(Seq(All("i", V("I")), Call("MeasurableSpace", App(V("Omega"), V("i")))))),
            Seq(All("mu", Seq(All("i", V("I")), Call("Measure", App(V("Omega"), V("i"))))),
                Instance(Seq(All("i", V("I")), Call("IsProbabilityMeasure", App(V("mu"), V("i"))))),
                All("F", new Formula.TypeArrow(Parenthesized(Product), Real)),
                Call("Measurable", V("F")), Sp, Rightarrow),
            Seq(All("M", Real), Open, All("x", Parenthesized(Product)),
                new Formula.Absolute(App(V("F"), V("x"))), Sp, Leq, Sp, V("M"), Close,
                Sp, Rightarrow),
            new Formula.Relation(Call("Var", V("F"), PiMeasure),
                FormulaRelationOperator.LessThanOrEqual,
                Multiply(new Formula.Fraction(D(1), D(2)),
                    Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, V("I"))), Sp, energy)))
        ]));
    }

}
