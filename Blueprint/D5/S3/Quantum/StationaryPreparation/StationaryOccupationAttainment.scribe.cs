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
                        "Here lower(r,i) subtracts one at coordinate i and leaves other coordinates " +
                        "unchanged, using natural truncated subtraction within the same box. " +
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
                        "alphabet-memory register. The identity V=tensorCoordinates composed with " +
                        "emissionCoordinates(a,head,e) fixes V to the coordinate transport of W. " +
                        "The action of U on blank head input agrees with V " +
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
        Formula sigma = F.Id("sigma"), a = F.Id("a"), head = F.Id("head");
        Formula r = F.Id("r"), s = F.Id("s"), b = F.Id("b"), j = F.Id("j");
        Formula h = F.Id("h"), i = F.Id("i"), k = F.Id("k"), x = F.Id("x");
        Formula e = F.Id("e"), v = F.Id("V"), u = F.Id("U"), w = F.Id("w");
        Formula zero = D(0), one = D(1), complex = F.Id("Complex");
        Formula nat = F.Id("Nat"), n = Call("N", a), max = Call("count", a, head);
        Formula box = Call("Box", a), tail = Call("Tail", a, head);
        Formula memory = Call("Space", Call("K", a, head));
        Formula finiteMemory = Call("Space", Call("Fin", n));
        Formula alphabet = Call("Space", sigma), multiset = Call("Multiset", sigma);
        Formula g = Call("G", a, head), matrix = Call("B", a, head), d = Call("D", a);
        Formula Ph(Formula q) => Call("phi", a, head, q);
        Formula Pf(Formula q) => Call("phiFin", a, head, e, q);
        Formula Im(Formula q) => Call("image", a, head, q);
        Formula Z(Formula q) => Call("z", head, q);
        Formula Occ(Formula q) => Call("occ", a, q);
        Formula Legal(Formula q) => Call("le", q, a);
        Formula M(Formula q) => Call("M", q);
        Formula Weight(Formula q) => Call("m", a, head, b, q);
        Formula Delta(Formula q) => Call("delta", a, head, b, q);
        Formula pred = Call("NatSub", j, one), ratio = Call("div", Weight(j), Weight(pred));
        Formula block = Call("block", a, head, b), lower = Call("L", max);
        Formula boundedHead = Call("Fin", Call("add", max, one));
        Formula blocks = All(Bound(b, tail), Both(
            Equal(block, Call("mul", Call("mul", lower,
                Call("diagonal", Lambda(j, Delta(Call("val", j))))), Call("transpose", lower))),
            Equal(Call("rank", block), Call("if", Equal(b, zero), one, Call("add", max, one))),
            Given(Equal(b, zero), Both(Equal(Weight(zero), one),
                All(Bound(j, nat), Equal(Delta(j), Call("if", Equal(j, zero), one, zero))))),
            Given(NotEqual(b, zero), Both(
                All(Bound(j, boundedHead), Call("lt", zero, Delta(Call("val", j)))),
                All(Bound(j, boundedHead), Equal(Call("lastTail", head,
                    Call("slice", a, head, b, Call("val", j))), Delta(Call("val", j)))))),
            All(Bound(j, nat), Given(Both(Call("le", one, j), Call("le", j, max)), Both(
                Equal(ratio, Call("div", Call("add", j, Call("card", Call("tailWord", a, head, b))), j)),
                Given(NotEqual(b, zero), Call("lt", one, ratio)))))));
        Formula Span(Formula space, bool transported) => Call("span", complex,
            Call("setOf", Bound(x, space), Some(Bound(r, multiset),
                Both(Legal(r), NotEqual(r, zero), Equal(x, transported ? Pf(r) : Ph(r))))));
        Formula Nonterminal(Formula space, bool transported) => Given(Call("lt", zero, max), Both(
            Equal(transported ? Pf(zero) : Ph(zero),
                transported ? Pf(Call("replicate", one, head)) : Ph(Call("replicate", one, head))),
            Equal(Span(space, transported), F.Id("top"))));
        Formula gram = Equal(Call("gram", Lambda(Bound(r, box), Ph(Occ(r)))), g);
        Formula initial = Pf(a), final = Pf(zero);
        Formula tensor = Call("TensorProduct", complex, alphabet, finiteMemory);
        Formula amplitude = Call("if", Equal(Call("occupation", w), a), Call("inv", Call("sqrt", M(a))), zero);
        Formula emission = Call("sum", Lambda(i, Call("smul",
            Call("sqrt", Call("div", Call("count", r, i), Call("card", r))),
            Call("tmul", Call("basis", i), Pf(Call("erase", r, i))))));
        Formula construction = Some(Bound(e, Call("Equiv", Call("K", a, head), Call("Fin", n))),
            Some(Bound(v, Call("LinearIsometry", complex, finiteMemory, tensor)),
            Some(Bound(u, Call("Unitary", Call("Product", sigma, Call("Fin", n)))), Both(
                Equal(v, Call("comp", Call("tensorCoordinates", n), Call("emissionCoordinates", a, head, e))),
                Equal(Call("gram", Lambda(Bound(r, box), Pf(Occ(r)))), g),
                Nonterminal(finiteMemory, true),
                All(Bound(x, finiteMemory), Equal(Call("apply", v, x), Call("apply", Call("tensorCoordinates", n),
                    Call("apply", u, Call("apply", Call("blankEmbed", n, head), x))))),
                All(Bound(r, multiset), Given(Both(Legal(r), NotEqual(r, zero)), Equal(Call("apply", v, Pf(r)), emission))),
                Equal(Call("apply", v, final), Call("tmul", Call("basis", head), final)),
                Equal(Call("norm", initial), one), Equal(Call("norm", final), one),
                All(Seq(Bound(w, Seq(Call("Fin", Call("card", a)), Sp, To, Sp, sigma)), Comma, Sp,
                    Bound(k, Call("Fin", n))), Equal(
                    Call("circuit", Call("const", u), Call("card", a), zero,
                        Call("initialized", head, Call("card", a), initial), Call("pair", w, k)),
                    Call("mul", amplitude, Call("coordinate", final, k))))))));
        Formula index = F.Id("J"), coeff = F.Id("c"), family = F.Id("rho");
        Formula SumImages(bool images) => Call("sum", Lambda(j,
            Call("smul", Call("apply", coeff, j), images ? Im(Call("apply", family, j)) : Ph(Call("apply", family, j)))));
        Formula relations = All(Bound(index, F.Id("Type")), Given(Call("Fintype", index),
            All(Seq(Bound(family, Seq(index, Sp, To, Sp, multiset)), Comma, Sp,
                Bound(coeff, Seq(index, Sp, To, Sp, complex))),
                Given(Both(All(Bound(j, index), Legal(Call("apply", family, j))), Equal(SumImages(false), zero)),
                    Equal(SumImages(true), zero)))));
        Formula recurrence = All(Seq(Bound(r, box), Comma, Sp, Bound(s, box)),
            Given(Both(NotEqual(Occ(r), zero), NotEqual(Occ(s), zero)), Equal(Call("entry", matrix, r, s),
                Call("sum", Lambda(i, Call("if", Both(Call("lt", zero, Call("val", Call("apply", r, i))),
                    Call("lt", zero, Call("val", Call("apply", s, i)))),
                    Call("entry", matrix, Call("lower", r, i), Call("lower", s, i)), zero))))));
        Formula body = Both(
            All(Bound(r, multiset), Equal(M(r), Call("NatDiv", Call("factorial", Call("card", r)),
                Call("prod", Lambda(i, Call("factorial", Call("count", r, i))))))),
            Equal(Z(zero), one),
            All(Bound(h, nat), Given(Both(Call("le", one, h), Call("le", h, max)), Equal(Z(Call("replicate", h, head)), one))),
            All(Bound(r, multiset), Given(Both(Legal(r), NotEqual(Call("tailOcc", head, r), zero)), Equal(Z(r), zero))),
            Call("Bijective", Lambda(Bound(r, box), Call("pair", Call("tailIndex", a, head, r), Call("apply", r, head)))),
            blocks, Equal(Call("card", Call("K", a, head)), n),
            All(Bound(r, multiset), Given(Legal(r), Equal(Call("norm", Ph(r)), one))), gram,
            All(Bound(r, multiset), Given(Legal(r), Equal(Call("inner", Ph(r), Ph(zero)), Z(r)))),
            Call("PosSemidef", g), Call("PosSemidef", matrix), Equal(Call("mul", Call("mul", d, g), d), matrix),
            Equal(Call("entry", matrix, zero, zero), one), Equal(Call("rank", g), n), Equal(Call("rank", matrix), n),
            Equal(Call("rank", matrix), Call("add", one,
                Call("mul", Call("NatSub", Call("card", tail), one), Call("add", max, one)))),
            recurrence,
            All(Seq(Bound(r, multiset), Comma, Sp, Bound(s, multiset)), Given(Both(Legal(r), Legal(s)),
                Equal(Call("inner", Im(r), Im(s)), Call("inner", Ph(r), Ph(s))))),
            relations, Nonterminal(memory, false),
            Given(Equal(a, zero), Both(Equal(n, one), Call("Nonempty", Call("LinearIsometryEquiv", complex, memory, complex)))),
            construction);
        return Disp(All(Bound(sigma, F.Id("Type")), Given(Both(Call("Fintype", sigma), Call("Nonempty", sigma)),
            All(Seq(Bound(a, multiset), Comma, Sp, Bound(head, sigma)),
                Given(Equal(max, Call("sup", Call("count", a))), body)))));
    }

    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula NotEqual(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);
    private static Formula Bound(Formula x, Formula type) => Seq(x, Colon, Sp, type);
    private static Formula Lambda(Formula x, Formula body) => Call("fun", x, body);
    private static Formula All(Formula x, Formula body) => Seq(Forall, Sp, x, Comma, Sp, body);
    private static Formula Some(Formula x, Formula body) => Seq(Exists, Sp, x, Comma, Sp, body);
    private static Formula Given(Formula premise, Formula result) => Seq(Open, premise, Close, Sp, Implies, Sp, Open, result, Close);
    private static Formula Both(params Formula[] clauses)
    {
        var result = Seq(Open, clauses[0], Close);
        foreach (var clause in clauses[1..])
            result = Seq(result, Sp, Land, Sp, Open, clause, Close);
        return Seq(Open, result, Close);
    }
}
