using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class SchwartzWeakAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact smooth tests characterize the adjoint of the actual Schwartz differential operator.",
        H("Compact Tests and the Schwartz Adjoint"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-schwartz-compact-adjoint-graph"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/SchwartzWeakAdjoint.compact_test_adjoint_graph"),
            H("The full differential sum has a densely defined symmetric Schwartz domain"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every natural dimension d, H is the actual complex Lebesgue L2 space "
                    + "on EuclideanSpace Real (Fin d). The coefficients a and b are arbitrary real functions "
                    + "on Fin d. J embeds a Schwartz function as its actual L2 class. The differential D is "
                    + "the finite sum of minus a of j times its second coordinate derivative plus b of j "
                    + "times coordinate j squared times the function.")),
                Paragraph(Text("S has precisely the range of J as its domain and sends J of phi to J of "
                    + "D phi. It has dense domain, is symmetric and is closable. For arbitrary L2 vectors "
                    + "f and g, Weak means that the inner product of J D psi with f equals that of J psi "
                    + "with g for every smooth compactly supported function psi on the actual Euclidean "
                    + "space, using its canonical Schwartz realization. Weak holds exactly when the pair f and g lies in the "
                    + "graph of the actual adjoint of S.")),
                Paragraph(Text("A compact smooth bump and simultaneous cutoff convergence of J psi and "
                    + "J D psi extend the identity to all Schwartz tests. Real bilinear integration by "
                    + "parts with conjugate z times w gives symmetry of the second derivatives. The real "
                    + "quadratic potential is symmetric pointwise. The closed adjoint contains S.")),
                Paragraph(Text("No derivative or potential term is required to be separately square "
                    + "integrable for f or g. Dimension zero and coefficients of either sign are included."))),
            DescribeRole.Theorem))));
    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), f = F.Id("f"), g = F.Id("g");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula s = Call("S", d, a, b);
        Formula graph = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("f"), Call("H", d)),
             new(FormulaIdentifier.Create("g"), Call("H", d))],
            new Formula.Logic(Call("Weak", d, a, b, f, g), FormulaLogicOperator.Iff,
                Call("GraphMember", Call("adjoint", s), f, g)));
        Formula conclusion = new Formula.Logic(Call("DenseDomain", s), FormulaLogicOperator.And,
            new Formula.Logic(Call("Symmetric", s), FormulaLogicOperator.And,
                new Formula.Logic(Call("Closable", s), FormulaLogicOperator.And, graph)));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("d"), F.Id("Nat")),
             new(FormulaIdentifier.Create("a"), new Formula.TypeArrow(Call("Fin", d), real)),
             new(FormulaIdentifier.Create("b"), new Formula.TypeArrow(Call("Fin", d), real))], conclusion);
    }
}
