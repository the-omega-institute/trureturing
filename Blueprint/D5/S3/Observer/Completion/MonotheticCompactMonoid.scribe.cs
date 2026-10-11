using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class MonotheticCompactMonoidDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Completion/MonotheticCompactMonoid.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/tanana2020compactmonothetic");
    private static Formula M => F.Id("M");
    private static Formula A => F.Id("a");
    private static Formula N => F.Id("n");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula G => F.Id("G");
    private static Formula R => F.Id("r");
    private static Formula T => F.Id("t");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ENat => Seq(Nat, Cup, OpenBrace, Infty, CloseBrace);
    private static Formula Type => Call("Type");
    private static Formula CoreSet => Call("core", A);
    private static Formula E => Val(Call("zero", G));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, y);
    private static Formula Mem(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(params Formula[] clauses) =>
        Seq(clauses.SelectMany((c, i) => i == 0 ? new[] { c }
            : new[] { Sp, Land, Sp, c }).ToArray());
    private static Formula Imp(Formula p, Formula q) => Seq(p, Sp, Rightarrow, Sp, q);
    private static Formula Fn(Formula x, Formula type, Formula body) =>
        Seq(Open, x, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula DenseOrbit(Formula a) =>
        Call("DenseRange", Fn(N, Nat, Call("nsmul", N, a)));
    private static Formula Base(Formula body) => All(M, Type, Seq(
        Inst("AddCommMonoid", M), Sp, Inst("TopologicalSpace", M), Sp,
        Inst("ContinuousAdd", M), Sp, Inst("CompactSpace", M), Sp, Inst("T2Space", M),
        Comma, Sp, All(A, M, Imp(DenseOrbit(A), body))));
    private static Formula Inherited(string op, Formula carrier) =>
        All(X, carrier, All(Y, carrier, Eqn(Val(Call(op, G, X, Y)),
            op == "add" ? Add(Val(X), Val(Y)) : Mul(Val(X), Val(Y)))));
    private static Formula Retraction(Formula carrier) => And(
        Call("Continuous", R),
        All(X, M, Eqn(Val(Call("r", X)), Add(X, E))),
        All(X, carrier, Eqn(Call("r", Val(X)), X)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dense additive orbit in a compact Hausdorff monoid has a minimal ideal group, "
        + "an isolated initial segment, and, for dense natural arithmetic, an internal ring.",
        H("The tail group of a compact monothetic monoid"),
        Blocks(
            Paragraph(Text(
                "The ambient addition is jointly continuous and commutative. The natural orbit "
                + "includes zero. The tail set carries the subspace topology; val denotes its "
                + "inclusion into the ambient space. A chosen internal structure G supplies its "
                + "own zero, addition and natural scalar multiplication. Its zero need not be "
                + "the ambient zero.")),
            Describe.Lean(DescribeId.Create("monothetic-tail"),
                DeclarationHandle.Create(Prefix + "tail"), H("Closed tails"),
                StatementSource.FromAuthor(Disp(All(M, Type, Seq(
                    Inst("AddCommMonoid", M), Sp, Inst("TopologicalSpace", M), Comma, Sp,
                    All(A, M, All(F.Id("k"), Nat,
                        Eqn(Call("tail", A, F.Id("k")), Call("closure", Call("range",
                            Fn(N, Nat, Call("nsmul", Add(F.Id("k"), N), A))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A tail starts at the indicated natural index and takes its closure."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("monothetic-core"),
                DeclarationHandle.Create(Prefix + "core"), H("The persistent tail"),
                StatementSource.FromAuthor(Disp(All(M, Type, Seq(
                    Inst("AddCommMonoid", M), Sp, Inst("TopologicalSpace", M), Comma, Sp,
                    All(A, M, Eqn(CoreSet, Call("iInter", Fn(N, Nat, Call("tail", A, N))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The core consists of the points in every closed tail."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("monothetic-core-structure"),
                DeclarationHandle.Create(Prefix + "core_structure"),
                H("Complete tail group and isolated initial segment"),
                StatementSource.FromAuthor(Disp(Base(And(GroupFormula(), IdealFormula())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Translation by any ambient point maps the core onto itself. "
                        + "Solving b+e=b inside the core produces an identity for every core point; "
                        + "solving x+y=e then produces inverses. The graph of inversion is closed. "
                        + "Compactness makes its projections closed, which proves continuity of inversion.")),
                    Paragraph(Text("The additive homomorphism r sends x to x+e and fixes the core. "
                        + "It is therefore onto. Its image of a is a+e, and its internal natural "
                        + "multiples are dense by continuity and density of the original orbit.")),
                    Paragraph(Text("Every nonempty additive ideal contains a point x and hence contains "
                        + "x+H=H. Thus H is the unique least nonempty additive ideal. It contains the "
                        + "ambient zero exactly when it is the whole monoid.")),
                    Paragraph(Text("The complement is the initial orbit segment below t, with t allowed "
                        + "to be infinity. Its points are pairwise distinct and isolated. Membership "
                        + "in H is upward closed in the natural index, so finite t is the first index "
                        + "whose orbit point enters H. If no index enters, t is infinity. A collision "
                        + "between two indices repeats arbitrarily far into the orbit and therefore lies in H.")),
                    Paragraph(Text("The classical comparison is Hewitt's compact monothetic semigroup "
                        + "structure theorem as stated in Tanana, Theorem 3, pages 15-16. The monoid "
                        + "form here explicitly includes the index zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("monothetic-ring-retraction"),
                DeclarationHandle.Create(Prefix + "core_ring_retraction"),
                H("Internal compact ring and unital semiring retraction"),
                StatementSource.FromAuthor(Disp(RingFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume a unital semiring whose addition and multiplication are "
                        + "jointly continuous, with dense natural casts. The zero ring is allowed. "
                        + "No additive cancellation, ambient additive inverse, or injectivity of "
                        + "natural casts is assumed. In this formula H means core(1), and every "
                        + "operation on H uses the displayed CommRing structure G.")),
                    Paragraph(Text("Commutativity extends from the dense natural casts. The internal "
                        + "zero e absorbs multiplication by every point of H: on the first tail, "
                        + "this follows from e times any positive natural cast being e, and then "
                        + "from continuity. Thus H is closed under multiplication, with unit 1+e. "
                        + "The identities e*x+e=e give multiplicativity of x mapped to x+e. The "
                        + "resulting continuous ring-valued semiring homomorphism preserves zero "
                        + "and one, is surjective, fixes H, and has dense natural unit multiples."))),
                DescribeRole.Theorem))));

    private static Formula GroupFormula() => Ex(G, Call("AddCommGroup", CoreSet), And(
        Inherited("add", CoreSet), Call("IsTopologicalAddGroup", CoreSet),
        Ex(R, Call("AddMonoidHom", M, CoreSet), And(Retraction(CoreSet),
            Call("DenseRange", Fn(N, Nat, Call("nsmul", G, N, Call("r", A))))))));

    private static Formula IdealFormula()
    {
        Formula ideal = F.Id("I");
        Formula indices = Call("set", Fn(N, Nat, Seq(N, Sp, Lt, Sp, T)));
        return And(Call("Nonempty", CoreSet), Call("IsCompact", CoreSet),
            All(X, M, Eqn(Call("image", Fn(Y, M, Add(X, Y)), CoreSet), CoreSet)),
            All(ideal, Call("Set", M), Imp(And(Call("Nonempty", ideal),
                All(X, M, All(Y, M, Imp(Mem(Y, ideal), Mem(Add(X, Y), ideal))))),
                Seq(CoreSet, Sp, Subseteq, Sp, ideal))),
            Seq(Mem(D(0), CoreSet), Sp, Iff, Sp, Eqn(CoreSet, Call("univ", M))),
            Seq(Exists, Bang, Sp, T, Colon, Sp, ENat, Comma, Sp, And(
                All(N, Nat, Seq(Neg, Sp, Mem(Call("nsmul", N, A), CoreSet), Sp, Iff, Sp,
                    N, Sp, Lt, Sp, T)),
                Eqn(Call("compl", CoreSet), Call("image", Fn(N, Nat, Call("nsmul", N, A)), indices)),
                Call("InjOn", Fn(N, Nat, Call("nsmul", N, A)), indices),
                All(N, Nat, Imp(Seq(N, Sp, Lt, Sp, T), Call("IsOpen",
                    Call("singleton", Call("nsmul", N, A))))))));
    }

    private static Formula RingFormula()
    {
        Formula h = Call("core", D(1));
        return All(M, Type, Seq(Inst("Semiring", M), Sp, Inst("TopologicalSpace", M), Sp,
            Inst("ContinuousAdd", M), Sp, Inst("ContinuousMul", M), Sp,
            Inst("CompactSpace", M), Sp, Inst("T2Space", M), Comma, Sp,
            Imp(DenseOrbit(D(1)), And(
                All(X, M, All(Y, M, Eqn(Mul(X, Y), Mul(Y, X)))),
                Ex(G, Call("CommRing", h), And(
                    Inherited("add", h), Inherited("mul", h),
                    Call("IsTopologicalRing", h), Call("CompactSpace", h),
                    Eqn(Val(Call("one", G)), Add(D(1), E)),
                    Ex(R, Call("RingHom", M, h), And(Retraction(h),
                        Call("Surjective", R), Call("DenseRange", Fn(N, Nat,
                            Call("nsmul", G, N, Call("one", G))))))))))));
    }
}
