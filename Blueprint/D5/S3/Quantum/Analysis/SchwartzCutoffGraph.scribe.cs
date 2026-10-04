using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class SchwartzCutoffGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scaled compact cutoffs converge in the actual Schwartz differential graph norm.",
        H("Schwartz Cutoff Graph Convergence"),
        Blocks(Describe.Lean(
            DescribeId.Create("scaled-schwartz-differential-graph-cutoff"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/SchwartzCutoffGraph.scaled_cutoff_graph"),
            H("Compact tests approximate the vector and the full differential sum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/pnt2026cutoffgraph")),
            Blocks(
                Paragraph(Text("For every natural dimension d, arbitrary real coordinate coefficients a and b, "
                    + "and complex Schwartz function f, let chi be a real Schwartz function with compact "
                    + "support, value one at zero and absolute value at most one everywhere. The functions "
                    + "psi of n equal chi applied to x divided by n plus one, times f of x. They are smooth "
                    + "and compactly supported. Their actual complex Lebesgue L2 vectors converge to f, "
                    + "and their differential images converge to the image of f.")),
                Paragraph(Text("The differential is the finite sum of minus a of j times the second "
                    + "coordinate derivative, plus b of j times the coordinate squared times the function. "
                    + "The physical coefficients are included. Dimension zero uses the empty sum.")),
                Paragraph(Text("The product rule gives both first derivative terms and the second cutoff "
                    + "derivative. Scaling bounds these terms by inverse powers of the radius. Squared "
                    + "dominated convergence gives the actual L2 limits. The cited W21 argument is "
                    + "one-dimensional and uses an L1 norm; the present statement extends its method."))),
            DescribeRole.Theorem))));
    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), f = F.Id("f"), c = F.Id("chi");
        Formula real = Seq(Mathbb, Grp(F.Id("R"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula e = Call("EuclideanSpace", real, Call("Fin", d));
        Formula psi = F.Id("psi"), n = F.Id("n"), x = F.Id("x");
        Formula pn = new Formula.Apply(psi, [n]);
        Formula scaled = new Formula.Fraction(x,
            new Formula.Binary(n, FormulaBinaryOperator.Add, D(1)));
        Formula values = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("n"), F.Id("Nat")), new(FormulaIdentifier.Create("x"), e)],
            Equal(new Formula.Apply(pn, [x]), new Formula.Binary(new Formula.Apply(c, [scaled]),
                FormulaBinaryOperator.Multiply, new Formula.Apply(f, [x]))));
        Formula support = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("n"), F.Id("Nat"))], Call("HasCompactSupport", pn));
        Formula limits = new Formula.Logic(Call("TendstoL2",
            new Formula.Sequence(Call("J", pn), n, F.Id("Nat")), Call("J", f)),
            FormulaLogicOperator.And, Call("TendstoL2",
                new Formula.Sequence(Call("J", Call("H", a, b, pn)), n, F.Id("Nat")),
                Call("J", Call("H", a, b, f))));
        Formula result = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("psi"), new Formula.TypeArrow(F.Id("Nat"), Call("Schwartz", e, complex)))],
            new Formula.Logic(values, FormulaLogicOperator.And,
                new Formula.Logic(support, FormulaLogicOperator.And, limits)));
        Formula bound = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("x"), e)],
            Seq(Vert, Sp, new Formula.Apply(c, [x]), Sp, Vert, Sp, Le, Sp, D(1)));
        Formula assumptions = new Formula.Logic(Call("HasCompactSupport", c), FormulaLogicOperator.And,
            new Formula.Logic(Equal(new Formula.Apply(c, [D(0)]), D(1)), FormulaLogicOperator.And, bound));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("d"), F.Id("Nat")),
             new(FormulaIdentifier.Create("a"), new Formula.TypeArrow(Call("Fin", d), real)),
             new(FormulaIdentifier.Create("b"), new Formula.TypeArrow(Call("Fin", d), real)),
             new(FormulaIdentifier.Create("f"), Call("Schwartz", e, complex)),
             new(FormulaIdentifier.Create("chi"), Call("Schwartz", e, real))],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, result));
    }
}
