using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class StationaryOccupationAttainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Last-tail padding realizes the exact occupation Gram blocks and one fixed preparation isometry.",
        H("Stationary Occupation Attainment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stationary-attainment-full"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/StationaryPreparation/StationaryOccupationAttainment.stationary_attainment_full"),
                H("General stationary attainment"),
                StatementSource.FromAuthor(AttainmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let sigma be any finite nonempty alphabet, let a be any multiset on sigma, " +
                        "and choose head with a.count(head) equal to the supremum of the counts. " +
                        "Write A for this maximum. Arbitrary natural capacities c are represented " +
                        "by the sum of c(i) copies of each i: this multiset has count c(i) at i " +
                        "and cardinality equal to the sum of c(i). No capacity is required to be positive. " +
                        "Box(a) consists of bounded counts r(i) in Fin(a.count(i)+1), and occ(r) " +
                        "is their multiset. M(r) counts the words with occupation r and equals " +
                        "r.card! divided by the product of r.count(i)! over the alphabet.")),
                    Paragraph(Text(
                        "Tail removes every copy of head. Set z(r)=1 when the tail of r is empty " +
                        "and z(r)=0 otherwise. Thus z(0)=1, z(h copies of head)=1 for 1<=h<=A, " +
                        "and every legal residual with nonempty tail has z(r)=0. The map from " +
                        "a bounded residual to its tail counts and head count is bijective. " +
                        "For a fixed tail b, put m(j)=M(j copies of head plus b) and delta(0)=m(0), " +
                        "delta(j)=m(j)-m(j-1) for j>0. The block B_b(j,k) is m(min(j,k)). " +
                        "Entries between distinct tail blocks are zero.")),
                    Paragraph(Text(
                        "Let L have ones on and below its diagonal and zeros elsewhere. Each block " +
                        "is exactly L diag(delta(0),...,delta(A)) L transpose. For the zero tail, " +
                        "m(0)=1 and the increments are 1 at zero and 0 at every positive index, " +
                        "so the block has rank 1. For every nonzero tail all increments are positive " +
                        "and the block has full rank A+1. For 1<=j<=A, the real ratio m(j)/m(j-1) " +
                        "equals (j+card(b))/j, and exceeds 1 when b is nonzero.")),
                    Paragraph(Text(
                        "The memory coordinates are one sink together with pairs (b,j), where b " +
                        "is a nonzero bounded tail and j lies in Fin(A+1). For a legal residual r " +
                        "with empty tail, padding(r) is the sink basis vector. For a nonempty tail b, " +
                        "its (b,j) coordinate is the square root of lastTail(j head+b) when " +
                        "j<=r.count(head), and all other coordinates vanish. Here lastTail(s) " +
                        "is card(tail(s))*M(s)/card(s), with real division. These weights equal " +
                        "delta(j) for every nonzero tail. Hence the actual padding vectors have " +
                        "exactly the displayed blocks, including their off-diagonal entries.")),
                    Paragraph(Text(
                        "Normalize padding(r) by 1/sqrt(M(r)) to obtain phi(r). Every legal phi(r) " +
                        "has norm 1. Its Gram matrix is G: if s<=r, the entry is " +
                        "sqrt(M(s)*M(r-s)/M(r))*z(r-s); if r<=s instead, use the complex conjugate " +
                        "of the reversed expression; incomparable pairs have entry zero. " +
                        "The inner product of phi(r) with phi(0) equals z(r). With D diagonal " +
                        "and D(r,r)=sqrt(M(r)), the exact congruence D G D=B holds. Both matrices " +
                        "are positive semidefinite, B(0,0)=1, and their common rank is the " +
                        "product of a.count(i)+1 minus A. This equals the memory cardinality " +
                        "and also 1+(card(Tail)-1)*(A+1).")),
                    Paragraph(Text(
                        "For two nonzero residuals r and s, B(r,s) is the sum over letters i of " +
                        "B(r-e(i),s-e(i)), retaining a term only when both counts at i are positive. " +
                        "The lowerings use natural truncated subtraction within the same box. " +
                        "Prescribe image(0)=head tensor phi(0), and for nonzero r prescribe " +
                        "image(r) as the sum of sqrt(r.count(i)/r.card) times i tensor phi(r.erase(i)). " +
                        "For every pair of legal residuals the prescribed images preserve their " +
                        "inner product. Consequently, for every finite index type J, every complex " +
                        "coefficient family c, and every legal residual family r, a zero sum " +
                        "of c(j)*phi(r(j)) gives a zero sum of c(j)*image(r(j)). This establishes " +
                        "preservation of all linear relations before constructing V.")),
                    Paragraph(Text(
                        "The padding transition emits head from the sink with probability one. " +
                        "For a state (b,h) with tail mass R>=2, its head probability is h/(h+R-1), " +
                        "and its probability for tail letter i is b(i)*(R-1)/(R*(h+R-1)). " +
                        "A head emission lowers h, and a tail emission lowers b(i). At R=1, " +
                        "positive h emits head with probability one; at h=0 the sole tail letter " +
                        "leads to the sink. Absent letters have probability zero. Under nonzero " +
                        "support, the emitted letter and successor recover the entire predecessor. " +
                        "The probabilities sum to one, so the weighted transition matrix W " +
                        "satisfies W conjugate-transpose times W=1. Its action on padding(r) " +
                        "in letter i is padding(r.erase(i)) for present i, and zero for absent i.")),
                    Paragraph(Text(
                        "If A>0 then phi(0)=phi(one copy of head), and the nonterminal residuals " +
                        "already span the whole memory. Choose a coordinate equivalence with " +
                        "Fin(N), where N is the rank above. There exist one isometry V from this " +
                        "memory to alphabet tensor the same memory, and one unitary U on the " +
                        "alphabet-memory register, whose action on blank head input agrees with V " +
                        "under the tensor coordinate isometry. V obeys the prescribed transition " +
                        "at every legal nonzero residual and sends phi(0) to head tensor phi(0). " +
                        "The coordinate transport preserves G and the nonterminal span.")),
                    Paragraph(Text(
                        "Initialize the memory at phi(a), blank all output registers with head, " +
                        "and use this same U at every step. For every word of length a.card and " +
                        "every final memory coordinate k, the circuit coefficient is " +
                        "phi(0)(k)/sqrt(M(a)) when the occupation is a and is zero otherwise. " +
                        "Both the initial vector and common final vector phi(0) are unit vectors. " +
                        "There is no additional memory or time-dependent control. When a=0, " +
                        "N=1 and the memory is linearly isometric to the complex numbers; " +
                        "the output statement includes the zero-length circuit."))),
                DescribeRole.Theorem))));

    private static Formula AttainmentFormula()
    {
        Formula a = F.Id("a");
        Formula head = F.Id("head");
        Formula i = F.Id("i");
        Formula n = F.Id("N");
        Formula e = F.Id("e");
        Formula w = F.Id("w");
        Formula k = F.Id("k");
        Formula initial = Call("phiFin", a, head, e, a);
        Formula final = Call("phiFin", a, head, e, D(0));
        Formula amplitude = Call("if", Seq(Call("occupation", w), Sp, Eq, Sp, a),
            Call("inv", Call("sqrt", Call("M", a))), D(0));
        Formula rank = Call("rank", Call("G", a, head));
        Formula cardinality = Seq(Prod, Underscore, Grp(i), Sp,
            Open, Call("count", a, i), Sp, Plus, Sp, D(1), Close);
        return Disp(Seq(
            Forall, Sp, F.Id("sigma"), Colon, Sp, F.Id("Type"), Comma, Sp,
            Open, Call("Fintype", F.Id("sigma")), Sp, Land, Sp,
            Call("Nonempty", F.Id("sigma")), Close, Sp, Implies, Esc,
            Forall, Sp, a, Colon, Sp, Call("Multiset", F.Id("sigma")), Comma, Sp,
            Forall, Sp, head, Colon, Sp, F.Id("sigma"), Comma, Sp,
            Call("count", a, head), Sp, Eq, Sp, Call("sup", Call("count", a)),
            Sp, Implies, Esc,
            n, Sp, Eq, Sp, Call("NatSub", cardinality, Call("count", a, head)),
            Sp, Eq, Sp, rank, Sp, Eq, Sp, Call("rank", Call("B", a, head)),
            Sp, Eq, Sp, Call("card", Call("K", a, head)), Comma, Esc,
            Call("B", a, head), Sp, Eq, Sp,
            Call("D", a), Sp, Call("G", a, head), Sp, Call("D", a), Comma, Esc,
            Exists, Sp, e, Colon, Sp, Call("Equiv", Call("K", a, head), Call("Fin", n)), Comma, Esc,
            Exists, Sp, F.Id("V"), Colon, Sp, Call("LinearIsometry", F.Id("Complex"),
                Call("Space", Call("Fin", n)), Call("TensorProduct", F.Id("Complex"),
                    Call("Space", F.Id("sigma")), Call("Space", Call("Fin", n)))), Comma, Esc,
            Exists, Sp, F.Id("U"), Colon, Sp,
            Call("Unitary", Call("Product", F.Id("sigma"), Call("Fin", n))), Comma, Esc,
            Forall, Sp, w, Colon, Sp, Call("Fin", Call("card", a)), Sp, To, Sp,
            F.Id("sigma"), Comma, Sp, k, Colon, Sp, Call("Fin", n), Comma, Esc,
            Call("circuit", Call("const", F.Id("U")), Call("card", a), D(0),
                Call("initialized", head, Call("card", a), initial), Call("pair", w, k)),
            Sp, Eq, Sp, amplitude, Sp, Call("coordinate", final, k), Dot));
    }
}
