using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class CharacteristicElevenDetourDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] xs) =>
        Seq(Op(name), Open,
            Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x }).ToArray()), Close);
    private static Formula All(string x, Formula ty, Formula body) =>
        Seq(Forall, Sp, Open, V(x), Colon, ty, Close, Comma, body);
    private static Formula Ex(string x, Formula ty, Formula body) =>
        Seq(Exists, Sp, Open, V(x), Colon, ty, Close, Comma, body);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Lam(string x, Formula ty, Formula body) =>
        Seq(Open, V(x), Colon, ty, Mapsto, Sp, body, Close);
    private static Formula Inst(string name, params Formula[] xs) =>
        Seq(OpenBracket, Call(name, xs), CloseBracket);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Ambient => Seq(Call("ZMod", D(1,1)), Times, Sp, V("K"));
    private static Formula Succ(Formula n) => Seq(n, Plus, D(1));
    private static Formula At(Formula n) => Call("v", n);
    private static Formula Edge(Formula n) => Seq(At(Succ(n)), Minus, At(n));
    private static Formula Outside => Seq(OpenBrace, V("z"), Colon, Ambient,
        Bar, Call("fst", V("z")), Neq, Sp, D(0), CloseBrace);
    private static Formula Prefix(Formula n) =>
        Seq(Sum, Underscore, Grp(V("i"), Lt, n), Edge(V("i")));

    private static Formula Statement()
    {
        Formula endpoints = Seq(At(D(0)), Eq, Pair(D(0), D(0)), Land, Sp,
            At(V("M")), Eq, Pair(D(0), V("u")));
        Formula injective = Call("Injective", Lam("n", Call("Fin", Succ(V("M"))), At(V("n"))));
        Formula interior = Call("BijOn", V("v"), Call("Ioo", D(0), V("M")), Outside);
        Formula labels = Call("BijOn", Lam("n", Nat, Edge(V("n"))), Call("Iio", V("M")),
            Seq(Outside, Cup, Sp, OpenBrace, Pair(D(0), V("u")), CloseBrace));
        Formula prefixes = Call("Injective",
            Lam("k", Call("Fin", Succ(V("M"))), Prefix(V("k"))));
        Formula intervals = All("a", Nat, All("b", Nat,
            Seq(V("a"), Lt, V("b"), Land, Sp, V("b"), Le, Sp, V("M"), Rightarrow, Sp,
                Sum, Underscore, Grp(V("a"), Le, Sp, V("i"), Lt, V("b")),
                Edge(V("i")), Neq, Sp, D(0))));
        Formula total = Seq(Prefix(V("M")), Eq, Pair(D(0), V("u")));
        Formula body = Ex("v", Seq(Nat, To, Sp, Ambient), Seq(endpoints, Land, Sp,
            injective, Land, Sp, interior, Land, Sp, labels, Land, Sp,
            prefixes, Land, Sp, intervals, Land, Sp, total));
        body = Seq(Op("let"), Sp, V("M"), Eq, D(1,0), Cdot, Call("card", V("K")), Plus, D(1), Semi, body);
        body = All("u", V("K"), Seq(V("u"), Neq, Sp, D(0), Rightarrow, Sp, body));
        return Disp(All("K", Op("Type"), Seq(Inst("Field", V("K")), Inst("Finite", V("K")),
            Inst("CharP", V("K"), D(1,1)), body)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translated ten-column action and exact relative paths in characteristic eleven",
        H("A translated ten-column relative path"), Blocks(
            Paragraph(Text("The ambient additive group is ZMod 11 times an arbitrary finite field K "
                + "of characteristic eleven. Fix any nonzero u in K. The construction uses every "
                + "nonzero first-coordinate vertex, including every zero row. It imposes no extension "
                + "degree or generator-choice restriction. This is the translated construction; "
                + "column translations are checked as actual affine maps and are not assumed to "
                + "preserve directed differences.")),
            Describe.Lean(DescribeId.Create("characteristic-eleven-relative-path"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/CharacteristicElevenDetour.exists_characteristic_eleven_relative_path"),
                H("Every finite characteristic-eleven field and every nonzero endpoint"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Put q=card(K), M=10q+1, B={(a,h):a is nonzero}, s=(0,0), "
                        + "and t=(0,u). The theorem supplies a natural-indexed vertex function v with "
                        + "v(0)=s and v(M)=t. Its M+1 bounded vertices are injective; its interior "
                        + "indices 0<n<M map bijectively onto B. Its M successive full vector "
                        + "differences map bijectively onto B union {(0,u)}. No value beyond the "
                        + "bounded path is prescribed. All M+1 bounded prefixes, including empty "
                        + "and full, are distinct. Every nonempty interval with 0<=a<b<=M has "
                        + "nonzero sum, and the full sum is (0,u).")),
                    Paragraph(Text("Choose a generator r of the cyclic unit group of K. Natural powers "
                        + "of r exhaust all units, order(r)=q-1, and a bounded positive power r^k=2 "
                        + "exists with 1<=k<=q-2. Characteristic eleven excludes 2=0, 2=1 and "
                        + "2=-1, so a generator cannot be -1. These are the only primitive exclusions "
                        + "needed by the translated lift.")),
                    Paragraph(Text("The columns are d=(1,2,4,8,5,10,9,7,3,6). Their shifts are "
                        + "b=(0,u,u,0,0,0,-2u,2u,0,(1+2/r)u). Coordinates (i,x) represent "
                        + "(d_i,(-1)^i*x+b_i). The skew product advances i without changing x "
                        + "until phase nine, then returns to phase zero with row r*x. Conjugation "
                        + "gives the actual nine maps h -> -h+b_i+b_(i+1) and closing map "
                        + "h -> -r*h+(r+2)u. The inverse uses the inverse skew product and the "
                        + "inverse coordinates. A ten-step return is multiplication by r. The "
                        + "published RowOrbitLift.row_same_cycle_iff supplies precisely the two "
                        + "row orbits: zero and all nonzero rows. All ten phases of both are retained.")),
                    Paragraph(Text("The heads (2,0),(1,2u),(7,0),(4,u) have normal coordinates "
                        + "(1,u),(0,2u),(7,2u),(2,0). On the long orbit the first three occur at "
                        + "times 1,10k,10k+7 in a traversal of length 10(q-1), in that strict order. "
                        + "The fourth head alone meets the zero-row orbit. Thus the actual first "
                        + "return is rho=(123)(4). For sigma=(1234), sigma*rho=(1324). The proof "
                        + "uses the published FiniteEndpointPairing.first_visit_reattach and "
                        + "same_cycle_of_first_visit and WeightedReattachment.untouched_reattach_iff. "
                        + "It proves every old orbit meets the cuts and that the induced return "
                        + "after endpoint insertion is a full six-cycle. Hence Q=(h1 s)(h1 t)*sigma*P "
                        + "is one cycle on the whole carrier, with Q(t)=s.")),
                    Paragraph(Text("The actual physical predecessors are (1,u),(6,u),(9,0),(2,u). "
                        + "Their old labels are (1,-u),(6,u),(9,0),(2,0). The rewired labels are "
                        + "(0,u),(1,-u),(6,u),(9,0), and the edge s -> h1 supplies (2,0). "
                        + "A permutation of the punctured tail carrier proves equality of the full "
                        + "label inventories with multiplicity one; every uncut edge remains. "
                        + "The artificial closing edge t -> s has label (0,-u) and is deleted. "
                        + "Mathlib's IsCycleOn enumeration gives all bounded indices and exact "
                        + "counts. Telescoping gives each prefix v(n)-v(0) and each interval "
                        + "v(b)-v(a); bounded vertex injectivity proves the interval and prefix clauses.")),
                    Paragraph(Text("The construction follows Characteristic eleven: row-return order and a translated ten-column lift, sections 2 and 4–6. This is a repository derivation of the specified translated "
                        + "construction using standard finite-field cyclicity and published orbit "
                        + "suppliers. No literature novelty is claimed. It proves only this full "
                        + "nonzero-column relative-path domain. The original arbitrary-subset "
                        + "parent and transport to its original coordinates remain open."))),
                DescribeRole.Theorem))));
}
