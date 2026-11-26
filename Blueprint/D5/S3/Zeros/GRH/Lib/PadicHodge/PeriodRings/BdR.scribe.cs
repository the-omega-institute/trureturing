using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings;

internal sealed class BdRDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bd R", H("Bd R"),
        Blocks(
            Paragraph(Text("The ideal W(m♭) and continuity of the Galois action on W(C♭) modulo p^m. Galois acts on [ε]−1 by the cyclotomic character modulo its square. Existence of Fontaine's period t with φt = pt, gt = χ(g)t, without logarithm. Frobenius contraction: solutions of ξ^n v = uφ(w) in A_max lie in A_inf[1/p]. B_dR with Galois action, embedding of Q̄_p; surjectivity in the fundamental exact sequence.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/BdR.fundamental_sequence_surjective"),
                H("fundamental_sequence_surjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Surjectivity in the fundamental exact sequence: for a in B and β in B_dR there is y in B with φ(y) − y = a and y − β in B_dR^+.")))))));
}
