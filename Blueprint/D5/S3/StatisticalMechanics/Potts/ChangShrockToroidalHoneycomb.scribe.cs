using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts;

internal sealed class ChangShrockToroidalHoneycombDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/changshrock2005toroidal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The labelled degree L-1 honeycomb transfer operator has eigenvalue v^(2(L-1))(v+q)^2 for every even L at least two.",
        H("An alternating vector for toroidal honeycomb strips"),
        Blocks(
            Definition("Coeff", Eq(N("Coeff"), Call("MvPolynomial", Call("Fin", D(2)), Z())),
                "Coeff is the polynomial ring over the integers with two independent variables indexed by Fin 2."),
            Definition("q", Eq(N("q"), Call("MvPolynomialX", D(0))),
                "The first polynomial indeterminate is the Potts component weight q."),
            Definition("v", Eq(N("v"), Call("MvPolynomialX", D(1))),
                "The second polynomial indeterminate is the Potts bond weight v."),
            Definition("Adjacent", All("L", Nat(), All("i", Sites(), All("j", Sites(),
                IffOf(Call("Adjacent", X("i"), X("j")), Or(
                    Eq(Call("mod", Add(Call("val", X("i")), D(1)), X("L")), Call("val", X("j"))),
                    Eq(Call("mod", Add(Call("val", X("j")), D(1)), X("L")), Call("val", X("i")))))))),
                "Sites are numbered from zero. Adjacency is symmetric and includes the cyclic seam."),
            Definition("Native", Width(All("f", Arrow(Sites(), Sites()),
                IffOf(Call("Native", X("L"), X("f")), NativeBody()))),
                "The nonzero symbols are the L-1 distinct marks. A bijective word represents singleton components, with symbol zero unmarked. "
                + "The second alternative replaces the zero at i by the mark at its cyclic neighbor j. The two equal symbols then encode one marked double block. "
                + "These are exactly the two possible block shapes with L sites and L-1 marked components. "
                + "Nonadjacent double blocks separate marked sites on both sides and violate the annular noncrossing condition. "
                + "For L=2 the seam has the same endpoints as the other bond. The bases (2.16) and (2.18) have respectively 3 and 48 labelled states."),
            Definition("State", Width(Eq(Call("State", X("L")), SetOf("f", Arrow(Sites(), Sites()),
                Call("Native", X("L"), X("f"))))),
                "State L retains the labelled connectivity word, with a proof that it is native. Equal words are the same diagram, including the two descriptions of a double block."),
            Definition("Space", Width(Eq(Call("Space", X("L")),
                Call("Finsupp", Call("State", X("L")), N("Coeff"))))),
                "Space L is the free module of polynomial coefficients on the native degree L-1 diagrams."),
            Definition("ket", Width(All("f", Arrow(Sites(), Sites()),
                Eq(Call("ket", X("f")), If(Call("Native", X("L"), X("f")),
                    Call("single", Call("subtype", X("f")), D(1)), D(0)))))),
                "A native connectivity word gives its unit basis vector. A word outside this degree block gives zero; the subtype proof carries no extra state information."),
            Definition("join", Width(All("i", Sites(), All("j", Sites(),
                Eq(Call("join", X("i"), X("j")), Call("linearCombination", N("Coeff"),
                    Fn("s", Call("State", X("L")), JoinBody()))))))),
                "Joining sites already in the same block changes nothing. An unmarked block takes the other block's mark when they merge. "
                + "Two different marks cannot be identified. The linear extension is over Coeff; s denotes the underlying connectivity word."),
            Definition("detach", Width(All("i", Sites(),
                Eq(Call("detach", X("i")), Call("linearCombination", N("Coeff"),
                    Fn("s", Call("State", X("L")), DetachBody())))))),
                "Closing the unmarked singleton multiplies by q. A site of a marked double block detaches to an unmarked singleton. "
                + "Removing a marked singleton loses a bridge and therefore projects to zero in this block."),
            Definition("vertical", Width(Eq(Call("vertical", X("L")),
                Call("ListProd", Call("ofFn", Fn("i", Sites(),
                    Add(Mul(N("v"), D(1)), Call("detach", X("i")))))))),
                "This is the ordered longitudinal product V of equation (2.34). ListProd multiplies endomorphisms by composition, in increasing site order."),
            Definition("horizontal", Width(All("b", N("Bool"),
                Eq(Call("horizontal", X("L"), X("b")),
                    Call("ListProd", Call("ofFn", Fn("k", Call("Fin", Call("div", X("L"), D(2))),
                        Add(D(1), Mul(N("v"), Call("join",
                            Call("ofNat", X("L"), Offset()),
                            Call("ofNat", X("L"), Add(Offset(), D(1)))))))))))),
                "The Boolean b selects the second bond layer. Its offset is one when true and zero when false. "
                + "Thus false pairs sites 0-1, 2-3 and so on; true pairs sites 1-2, 3-4 and the seam L-1 to 0. "
                + "Fin.ofNat reduces site numbers modulo L. These are the two honeycomb H operators in equation (2.34)."),
            Definition("transfer", Width(Eq(Call("transfer", X("L")),
                Mul(Mul(Call("vertical", X("L")), Call("horizontal", X("L"), N("true"))),
                    Mul(Call("vertical", X("L")), Call("horizontal", X("L"), N("false"))))))),
                "Equation (2.35) defines T=(V Htwo)(V Hone). The operator acts on the full native labelled degree L-1 block, including double-block states.", true),
            Definition("alternatingVector", Width(Eq(Call("alternatingVector", X("L")),
                Seq(Script(Sum, "s", Call("Perm", Sites())), Sp,
                    Call("single", Call("subtype", X("s")), Call("IntCast", Call("PermSign", X("s"))))))),
                "The sum runs over all permutations of the L symbols. Its singleton-state coefficient is the integer sign, embedded in Coeff. "
                + "The identity permutation contributes coefficient one, and no other permutation represents that labelled singleton diagram."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The eigenvalue at every even width"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let w be the alternating singleton vector. For two distinct adjacent sites, interchange their symbols. "
                        + "The permutation sign reverses. If both symbols are marks, the join is zero. If one is zero, both arrangements give the same marked double block. "
                        + "Consequently the join contributions cancel in pairs, including across the cyclic seam, so each transverse layer fixes w.")),
                    Paragraph(Text("On any singleton arrangement, detaching a marked site is zero and detaching the unique unmarked site contributes q. "
                        + "The longitudinal product therefore multiplies every such basis vector by v^(L-1)(v+q). "
                        + "Applying the two longitudinal layers and the two transverse layers gives v^(2(L-1))(v+q)^2 times w. "
                        + "The identity coefficient proves w is nonzero over the polynomial ring itself; no division by v or specialization of q is used."))),
                DescribeRole.Theorem))));

    private static Formula NativeBody() => Or(
        Ex("s", Call("Perm", Sites()), Eq(X("f"), X("s"))),
        Ex("s", Call("Perm", Sites()), Ex("i", Sites(), Ex("j", Sites(),
            And(Ne(X("i"), X("j")), And(Call("Adjacent", X("i"), X("j")),
                And(Eq(At(X("s"), X("i")), D(0)),
                    Eq(X("f"), Call("update", X("s"), X("i"), At(X("s"), X("j"))))))))));
    private static Formula JoinBody() => If(Eq(Site("i"), Site("j")), Call("single", X("s"), D(1)),
        If(Eq(Site("i"), D(0)), Call("ket", Call("update", X("s"), X("i"), Site("j"))),
            If(Eq(Site("j"), D(0)), Call("ket", Call("update", X("s"), X("j"), Site("i"))), D(0))));
    private static Formula DetachBody() => If(Eq(Site("i"), D(0)),
        Mul(N("q"), Call("single", X("s"), D(1))),
        If(Ex("j", Sites(), And(Ne(X("j"), X("i")), Eq(Site("j"), Site("i")))),
            Call("ket", Call("update", X("s"), X("i"), D(0))), D(0)));
    private static Formula ResultFormula() => All("L", Nat(),
        Arrow(new Formula.Relation(D(2), X("L"), FormulaRelationOperator.LessThanOrEqual),
            Arrow(Call("Even", X("L")), Ex("w", Call("Space", X("L")),
                And(Ne(X("w"), D(0)), Eq(At(Call("transfer", X("L")), X("w")),
                    Mul(Power(N("v"), Mul(D(2), Sub(X("L"), D(1)))),
                        Mul(Power(Add(N("v"), N("q")), D(2)), X("w")))))))));
    private static Formula Offset() => Add(Mul(D(2), Call("val", X("k"))), If(X("b"), D(1), D(0)));
    private static Formula Site(string name) => At(X("s"), X(name));
    private static DocumentBlock Definition(string name, Formula formula, string text, bool literature = false) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula Width(Formula body) => All("L", Nat(), Seq(OpenBracket, Call("NeZero", X("L")), CloseBracket, Sp, body));
    private static Formula Sites() => Call("Fin", X("L"));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Z() => Seq(Mathbb, Grp(X("Z")));
    private static Formula X(string name) => F.Id(name);
    private static Formula N(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) => At(N(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Par(a), Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Add, Par(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Subtract, Par(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Par(a), Par(b));
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("ite", condition, yes, no);
    private static Formula Bound(string name, Formula type) => Par(Seq(X(name), Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Bound(name, type), Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Bound(name, type), Comma, Sp, Par(body));
    private static Formula Fn(string name, Formula type, Formula body) => Par(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, Bound(name, type), Sp, Mid, Sp, body, CloseBrace);
    private static Formula Script(Formula op, string name, Formula type) => Seq(op, Subscript(Seq(X(name), Sp, InMacro, Sp, type)));
}
