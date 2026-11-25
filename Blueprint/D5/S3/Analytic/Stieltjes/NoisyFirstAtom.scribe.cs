using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Stieltjes;

internal sealed class NoisyFirstAtomDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Stieltjes/NoisyFirstAtom.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite set of noisy samples of a normalized positive Stieltjes transform bounds its smallest atom.",
        H("Enclosing the first atom from noisy Stieltjes samples"),
        Blocks(
            Describe.Lean(DescribeId.Create("signed-difference"), DeclarationHandle.Create(Prefix + "difference"),
                H("Signed forward difference"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At order zero take the initial sample. At each higher order subtract the same difference on the grid shifted by one node."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pole-product"), DeclarationHandle.Create(Prefix + "poleProduct"),
                H("Product over positive grid nodes"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P is the product of x+jh for j from 1 to k. The empty product equals one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("noisy-first-atom"), DeclarationHandle.Create(Prefix + "noisy_first_atom_enclosure"),
                H("Finite-precision enclosure of the first atom"),
                StatementSource.FromAuthor(Disp(Seq(D(1), Sp, Le, Sp, F.Id("S"), F.Id("a"), F.Id("P"),
                    Open, F.Id("D"), Plus, F.Id("e"), Close, Comma, Esc,
                    F.Id("P"), Open, F.Id("D"), Minus, F.Id("e"), Close, Sp, Le, Sp, D(1)))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a be the smallest positive atom of a discrete probability distribution. Its masses p_i are nonnegative, their sum is one, and the mass p_0 at a satisfies S a p_0 ≥ 1 for a known S > 0. The normalized reading at u is the sum of p_i b_i/(b_i+u). On the equally spaced grid starting at zero with step h > 0 the first reading is known exactly as one. Each of the k positive-node readings has absolute error at most ε.")),
                    Paragraph(Text("D is the order-k signed difference of the measured grid divided by k! h^k. Its error bound e equals (2^k−1)ε/(k! h^k), and P denotes the positive-node product at a. The difference of each exact single-atom resolvent contributes the inverse product of b_i+jh over j from 1 to k. Absolute summability permits the finite difference to pass through the sum. Each term lies below its mass times the inverse product at a, and retaining the first term gives the other inequality.")),
                    Paragraph(Text("For positive k, monotonicity gives a lower endpoint for a from the first inequality. The second gives a finite upper endpoint when D−e is positive and the data are consistent."))),
                DescribeRole.Theorem))));
}
