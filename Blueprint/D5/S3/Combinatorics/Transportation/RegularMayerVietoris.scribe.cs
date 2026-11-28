using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class RegularMayerVietorisDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Semigroups/goodearlpardowehrung2004semilattices");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under regularity, conicality and the three idempotent-component laws characterize exact finite-fiber transportation.",
        H("Regular Mayer–Vietoris Transportation"),
        Blocks(Describe.Lean(
            DescribeId.Create("regular-mvp-finite-fiber-transport"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/RegularMayerVietoris.regular_mvp_iff_finite_fiber_transport"),
            H("The exact transportation equivalence"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("K is an arbitrary AddCommMonoid satisfying regularity: for every x there is y with x+y+x=x. Write I(e) for e+e=e, L(x,y) for existence of t with x+t=y, and C(e,x) for L(e,x) and L(x,e). I and C in the displayed formula abbreviate precisely these definitions. No ambient order is used, and the component identity e need not be the global zero.")),
                Paragraph(Text("The left side has four clauses: conicality; refinement of any equality between sums of two idempotents into four idempotent entries; C(e+f,x) exactly when x decomposes into a representative of the e-component plus one of the f-component; and a common lift w of u and v whenever C(e,u), C(f,v), and u+f=v+e. Distributivity here means idempotent refinement and does not require meets.")),
                Paragraph(Text("The right side quantifies over independently universed finite types A and B, including empty types, and an arbitrary type Z. fiberSum(f,p,h) means the sum over A of p(a) if f(a)=h and zero otherwise. A matrix in the original K is zero on mismatched labels and has every prescribed row and column sum. There is no finite K, cancellation, multiplication, normalization, nonempty carrier, nontriviality, embedding, or purity premise.")),
                Paragraph(Text("Goodearl, Pardo and Wehrung, Lemma 2.1, supply the regular component construction; Theorem 3.2 supplies the refinement classification. Necessity takes the idempotent identities of refinement entries, offsets a refinement of x plus its internal inverse to obtain component-sum surjectivity, and adds the inverse of the lower-right entry to the upper-left entry to obtain a common lift. Sufficiency refines the four component identities, decomposes each row, forms the column defects, and lifts their compatible pair. Splitting that lift under the two row identities gives two row corrections. Their internal inverses correct the first column and the corrections themselves correct the second column, preserving both rows.")),
                Paragraph(Text("Closure of idempotent sums is supplied directly by the pinned Mathlib theorem IsIdempotentElem.mul on Multiplicative K. This type tag changes the notation for the same operation; both the component proof and the final matrix equalities remain in the original additive monoid.")),
                Paragraph(Text("A concrete coefficient example is Additive (WithOne (Multiplicative (ZMod 2))), the two-element additive group with a new global identity adjoined. It has three elements: global zero, an embedded local identity e, and an element x with e nonzero, e+x=x, x+x=e, and x+x distinct from x. It is regular, conical, and has binary refinement, so the criterion gives finite-fiber transportation. In contrast, ZMod 2 itself is regular but is not conical: two weights equal to one sum to zero. On a two-element source and an empty target with constant label, fiber totals agree but every matrix row sums to zero, so those nonzero marginals cannot be transported.")),
                Paragraph(Text("The predecessor exact transportation equivalence is applied directly to this refinement construction and conicality. The result is an acquisition of the published classification and its transportation consequence. It does not settle the separate largest-support classification problem and makes no mathematical originality claim."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula SumAt(string name, Formula carrier, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(V(name), Sp, InMacro, Sp, carrier)), Sp, body);
    private static Formula Instance(string name, Formula carrier, Formula body) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket, Comma, Sp, body);

    private static Formula Statement()
    {
        Formula k=V("K"), a=V("a"), b=V("b"), c=V("c"), d=V("d");
        Formula x=V("x"), y=V("y"), r=V("r"), s=V("s"), t=V("t"), u=V("u");
        Formula conical = All("x", k, All("y", k,
            Imp(Eq(Add(x,y),D(0)), And(Eq(x,D(0)),Eq(y,D(0))))));
        Formula matrix = And(Eq(Add(r,s),a), And(Eq(Add(t,u),b),
            And(Eq(Add(r,t),c),Eq(Add(s,u),d))));
        Formula ie=Call("I",a), iff=Call("I",b);
        Formula idem = All("a",k,All("b",k,All("c",k,All("d",k,
            Imp(And(ie,And(iff,And(Call("I",c),And(Call("I",d),Eq(Add(a,b),Add(c,d)))))),
                Some("r",k,Some("s",k,Some("t",k,Some("u",k,
                    And(Call("I",r),And(Call("I",s),And(Call("I",t),And(Call("I",u),matrix)))))))))))));
        Formula sums = All("a",k,All("b",k,Imp(And(ie,iff),All("x",k,
            Logic(Call("C",Add(a,b),x),FormulaLogicOperator.Iff,
                Some("u",k,Some("v",k,And(Call("C",a,u),And(Call("C",b,V("v")),Eq(Add(u,V("v")),x))))))))));
        Formula lifts = All("a",k,All("b",k,All("u",k,All("v",k,
            Imp(And(ie,And(iff,And(Call("C",a,u),And(Call("C",b,V("v")),Eq(Add(u,b),Add(V("v"),a)))))),
                Some("w",k,And(Eq(Add(V("w"),a),u),Eq(Add(V("w"),b),V("v")))))))));
        Formula regular = All("x",k,Some("y",k,Eq(Add(Add(x,y),x),x)));
        Formula ac=V("A"), bc=V("B"), z=V("Z");
        Formula f=V("f"), g=V("g"), p=V("p"), q=V("q"), m=V("m"), h=V("h");
        Formula agree=All("h",z,Eq(Call("fiberSum",f,p,h),Call("fiberSum",g,q,h)));
        Formula vanish=All("a",ac,All("b",bc,
            Imp(Ne(Call("f",a),Call("g",b)),Eq(Call("m",a,b),D(0)))));
        Formula rows=All("a",ac,Eq(SumAt("b",bc,Call("m",a,b)),Call("p",a)));
        Formula cols=All("b",bc,Eq(SumAt("a",ac,Call("m",a,b)),Call("q",b)));
        Formula witness=Some("m",Arrow(ac,Arrow(bc,k)),And(vanish,And(rows,cols)));
        Formula transport=All("A",V("Type"),All("B",V("Type"),All("Z",V("Type"),
            Instance("Fintype",ac,Instance("Fintype",bc,
                All("f",Arrow(ac,z),All("g",Arrow(bc,z),All("p",Arrow(ac,k),All("q",Arrow(bc,k),
                    Imp(agree,witness))))))))));
        return All("K",V("Type"),Instance("AddCommMonoid",k,
            Imp(regular,Logic(And(conical,And(idem,And(sums,lifts))),FormulaLogicOperator.Iff,transport))));
    }
}
