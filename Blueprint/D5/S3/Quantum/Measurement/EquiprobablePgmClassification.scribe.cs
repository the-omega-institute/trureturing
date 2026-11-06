using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmClassification.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual symmetric optimal measurements", H("Complete actual symmetric optimal measurements"), Blocks(
            Node("basisFlip", "Exchange the two basis coordinates", DescribeRole.Definition,
                "The actual linear matrix reindexing M(i,j) -> M(rev i,rev j) exchanges the two orthonormal qubit basis vectors. The proof checks positivity, POVM completeness, actual score invariance and the involution; no scalar symmetry bridge is assumed."),
            Node("lowerPovm", "The negative-sign three-active measurement", DescribeRole.Definition,
                "For t=b/(a-c), the effects are the basis flips of upperPovm(t). Equivalently E_+=[[1,t],[t,t^2]]/2, E_-=[[1,-t],[-t,t^2]]/2 and E_3=diag(0,1-t^2). In the strict lower region b<a-c, all effects are nonzero."),
            Node("lower_classification", "Unique optimum in the negative-sign region", DescribeRole.Theorem,
                "For every a,b,c with 0<b<a-c, the actual lowerPovm(b/(a-c)) is a finitePOVM with success (1+a-c+b^2/(a-c))/3. Every actual complex finitePOVM E is optimal if and only if it equals that measurement. This is derived by an actual basis permutation from the upper classification, transporting all competitors as well as the candidate."),
            Node("optimalPovm", "The full piecewise actual optimizer", DescribeRole.Definition,
                "Use pairPovm when |c-a|<=b, upperPovm(b/(c-a)) when c-a>b, and lowerPovm(b/(a-c)) otherwise. Both equality boundaries are assigned to the unique pair optimum. On the strict density domain 0<a,c<1, 0<b<sqrt(a(1-a)), these are exactly the note’s two-active and three-active effects, in the original label order."),
            Node("complete_classification", "Every optimum and its exact active set", DescribeRole.Theorem,
                "For every b>0 the actual optimalPovm is a finitePOVM, and an arbitrary actual finitePOVM E is optimal among all complex finitePOVMs if and only if E=optimalPovm. Its active set, defined by nonzero effects, is exactly {0,1} when |c-a|<=b and is all three labels otherwise. The physical strict-density theorem is supplied separately by states_posDef; the optimization calculation itself uses no extra positivity assumption on a or c. In the three-active regions the exact success from the two orientation theorems is (1+R)/3 with R=((c-a)^2+b^2)/|c-a|. Both signs and the two equality boundaries are included."),
            Paragraph(Text("Sources: anonymous mechanism manuscript (3 November 2026, anonymous author field, no supplied license grant); the new note by Haobo Ma then Wenlin Zhang (4 November 2026, new-note-only CC BY 4.0); the literal old byline Wenlin Zhang and Haobo / trureturing. Hyunho Cha credits for symmetric scores and qubit/commuting constructions are retained. The old rational refutation is reused without a new proof. The general all-pure and positive-spectral-floor comparisons remain unresolved by these sources."))
        ), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("equiprobablepgmclassification-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/mazhang2026pgmratio")),
        Blocks(Paragraph(Text(prose))), role);
}
