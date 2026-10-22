using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostStressCurrentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostStressCurrent.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/eholzer1997ghost");
    private static Formula Quantifiers() => Seq(
        Forall, Sp, F.Id("K"), Colon, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Sp,
        Forall, Sp, F.Id("m"), Comma, F.Id("n"), InMacro, Sp,
        Seq(Mathbb, Grp(F.Id("Z"))), Comma, Esc);
    private static Formula Mode(string name, Formula index) => Call(name, F.Id("K"), index);
    private static Formula SumIndex() => Seq(F.Id("m"), Plus, F.Id("n"));
    private static Formula Commutator(string current) => Seq(
        Mode("L", F.Id("m")), Sp, Mode(current, F.Id("n")), Minus,
        Mode(current, F.Id("n")), Sp, Mode("L", F.Id("m")));
    private static Formula Anticommutator(string left, string right) => Seq(
        Mode(left, F.Id("m")), Sp, Mode(right, F.Id("n")), Plus,
        Mode(right, F.Id("n")), Sp, Mode(left, F.Id("m")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual ghost stress tensor acts on b and c with conformal weights two and minus one on every state.",
        H("All-State Ghost Stress-Current Covariance"),
        Blocks(
            Paragraph(Text("K is any commutative ring and Fock(K) is the finite-support sum "
                + "over all finite subsets of the natural numbers. At b-mode m<=-2, create "
                + "at site 2(-m-2); otherwise delete at site 2(m+1)+1. At c-mode n<=1, "
                + "create at site 2(1-n)+1; otherwise delete at site 2(n-2). In each branch "
                + "the indicated natural site is the nonnegative integer value of its expression. "
                + "Insertion and deletion use the parity of occupied lower sites.")),
            Paragraph(Text("Write N(p,q)=b_p c_q for p<=-2 and N(p,q)=-c_q b_p otherwise. "
                + "The genuine linear stress operator is L_m v=sum_k (m-k) N(m+k,-k)v. "
                + "Each input has a finite normal-ordering support interval; the sum defines "
                + "an operator on the full carrier without a uniform cutoff.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-b-b-car"),
                DeclarationHandle.Create(Prefix + "b_b"),
                H("The b-modes anticommute"),
                StatementSource.FromAuthor(Disp(Seq(Quantifiers(),
                    Anticommutator("b", "b"), Eq, D(0)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every commutative ring K and all integers m,n, "
                    + "b_m b_n+b_n b_m=0 in Module.End K (Fock K). The equality uses "
                    + "the actual signed insertion and deletion operators on all finite "
                    + "superpositions of finite subsets, not an assumed CAR representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-c-c-car"),
                DeclarationHandle.Create(Prefix + "c_c"),
                H("The c-modes anticommute"),
                StatementSource.FromAuthor(Disp(Seq(Quantifiers(),
                    Anticommutator("c", "c"), Eq, D(0)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every commutative ring K and all integers m,n, "
                    + "c_m c_n+c_n c_m=0 in Module.End K (Fock K), for the same "
                    + "concrete carrier and signed operators."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-b-c-car"),
                DeclarationHandle.Create(Prefix + "b_c"),
                H("The mixed anticommutator is the identity at opposite modes"),
                StatementSource.FromAuthor(Disp(Seq(Quantifiers(),
                    Anticommutator("b", "c"), Eq,
                    Call("delta", SumIndex(), D(0)), Sp, D(1)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every commutative ring K and all integers m,n, "
                    + "b_m c_n+c_n b_m=if m+n=0 then 1 else 0 in Module.End K (Fock K). "
                    + "Here delta_(m+n,0) is one exactly when m+n=0 and zero otherwise; "
                    + "1 is the identity endomorphism. No field, nontriviality or "
                    + "characteristic assumption is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-stress-b-covariance"),
                DeclarationHandle.Create(Prefix + "L_b_commutator"),
                H("The b-current has weight two"),
                StatementSource.FromAuthor(Disp(Seq(Quantifiers(), Commutator("b"), Eq,
                    Grp(Open, F.Id("m"), Minus, F.Id("n"), Close), Sp, Mode("b", SumIndex())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every commutative ring K and integers m,n, "
                    + "L_m b_n-b_n L_m=(m-n)b_(m+n) as K-linear endomorphisms. "
                    + "Equivalently the equality holds on every finite superposition of arbitrary "
                    + "finite subsets. The scalar is the integer mapped into K. There are no "
                    + "field, nontriviality or characteristic assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-stress-c-covariance"),
                DeclarationHandle.Create(Prefix + "L_c_commutator"),
                H("The c-current has weight minus one"),
                StatementSource.FromAuthor(Disp(Seq(Quantifiers(), Commutator("c"), Eq,
                    Grp(Open, Minus, D(2), F.Id("m"), Minus, F.Id("n"), Close), Sp,
                    Mode("c", SumIndex())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every commutative ring K and integers m,n, "
                    + "L_m c_n-c_n L_m=(-2m-n)c_(m+n) as K-linear endomorphisms "
                    + "of exactly the same full carrier, with integer scalar mapped into K."))),
                DescribeRole.Theorem),
            Paragraph(Text("The exterior-coordinate equivalence identifies create_i with "
                + "left multiplication by the exterior generator at i and annihilate_i with "
                + "contraction by its coordinate functional. These are the concrete "
                + "exterior_create and exterior_annihilate identities. Exterior multiplication "
                + "and contraction give creation-creation and contraction-contraction "
                + "anticommutation and the mixed Kronecker identity over any commutative ring. "
                + "Splitting at b-mode -2 and c-mode 1 and checking the natural site indices "
                + "gives the three integer-mode CAR. They in turn give "
                + "[N(p,q),b_n]=delta_(q+n,0)b_p and "
                + "[N(p,q),c_n]=-delta_(p+n,0)c_q. For each input v the two stress sums "
                + "are evaluated in one interval enclosing the support for v, the support "
                + "for the current applied to v, and the single surviving index. Linearity "
                + "transports the finite sum and the CAR collapse it to that index. This "
                + "argument uses the actual statewise support theorem.")),
            Paragraph(Text("Eholzer, Feher and Honecker, section 2 of hep-th/9708160, gives "
                + "the conformal weights in equation (2.5), the Fock/CAR conventions in "
                + "equations (2.7)-(2.10), and the stress-tensor modes in equation (2.15). "
                + "The physical labels here are "
                + "b_math(m+1) and c_math(n-2) in uniform vertex-algebra mode notation, "
                + "which explains the coefficient m-k. These covariance laws do not establish "
                + "the all-state Virasoro central charge -26, vacuum invariance, BRST "
                + "cohomology, string amplitudes, Monster moonshine or AdS/CFT.")))));
}
