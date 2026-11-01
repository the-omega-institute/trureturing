using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin;

internal sealed class ClassicalPerfectTensorFactorizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/FiniteGeometry/pozsgaywanless2024tensor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every three-gate factorization of a classical six-leg perfect tensor has perfect two-wire factors.",
        H("Classical perfect tensors have perfect factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("index-one-oa"),
                DeclarationHandle.Create(Module + ".IsIndexOneOA"),
                H("Index-one orthogonal arrays"),
                StatementSource.FromAuthor(Disp(ArrayFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The row type r and symbol type x lie in independent arbitrary universes v and u; "
                    + "universe levels are implicit parameters throughout. For finite r and x, rows assigns "
                    + "one symbol to each row and column. "
                    + "Every ordered selection cols of s distinct columns must give a bijection from rows to s-tuples of symbols. "
                    + "Thus each tuple occurs exactly once. This is the orthogonality condition of factoringtriunit.tex, "
                    + "lines 891–902. The source also specifies the row count as the alphabet size to the power s; "
                    + "here that count follows whenever a selection of s distinct columns exists. "
                    + "If s exceeds c, there is no such selection and the predicate is vacuous."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gate-graph"),
                DeclarationHandle.Create(Module + ".gateGraph"),
                H("The four-column graph of a gate"),
                StatementSource.FromAuthor(Disp(GateFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A gate f sends two input symbols to two output symbols. Its graph records the inputs first, "
                    + "then the outputs, in columns numbered zero through three. This is the four-leg instance "
                    + "of the classical-map array in factoringtriunit.tex, lines 929–937, and the smaller arrays "
                    + "of lines 960–964. Perfection means that every pair of columns contains every ordered "
                    + "pair of symbols exactly once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circuit"),
                DeclarationHandle.Create(Module + ".circuit"),
                H("Three gates on three wires"),
                StatementSource.FromAuthor(Disp(CircuitFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The first gate a acts on wires one and two, producing ab. The second gate b acts on "
                    + "the first output of a and wire three, producing pc. The last gate c acts on the second "
                    + "output of a and the second output of b, producing qr. The final outputs are the first "
                    + "coordinate of pc and the two coordinates of qr. This is the order of composition "
                    + "in factoringtriunit.tex, lines 945–960, equation (4.2). Triples are pairs whose second "
                    + "coordinate is itself a pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circuit-graph"),
                DeclarationHandle.Create(Module + ".circuitGraph"),
                H("The six-column circuit graph"),
                StatementSource.FromAuthor(Disp(CircuitGraphFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The six columns record the three inputs followed by the three circuit outputs. "
                    + "Rows are indexed by all input triples. This is the array associated with the classical "
                    + "map in factoringtriunit.tex, lines 929–937 and 945–955. Strength three says that any "
                    + "three distinct columns determine the input triple uniquely and attain every symbol triple."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Perfection descends to the three factors"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(FactorizationStatement())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every finite alphabet x and arbitrary gates a, b and c, "
                    + "strength three of the circuit graph implies strength two of each gate graph. "
                    + "This formulates the nonlinear classical question in factoringtriunit.tex, lines 1196–1200, "
                    + "using the composition of equation (4.2). No linearity, field structure, initial "
                    + "bijectivity or dual unitarity is assumed for the factors. The statement includes "
                    + "empty alphabets. It asserts a property of any such factorization, without asserting "
                    + "that a factorization exists or that perfect factors always have a perfect composite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Every classical factor is perfect"),
                StatementSource.FromAuthor(Disp(FactorizationStatement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For any three distinct columns, equality of their entries forces equality of rows, "
                        + "and every prescribed triple of entries occurs. A two-wire gate is perfect if it "
                        + "is bijective and each output coordinate is bijective in each input separately. "
                        + "Indeed, two input columns determine the input directly; one input and one output "
                        + "use the corresponding one-variable bijection; two output columns use bijectivity "
                        + "of the gate. These give injectivity for every two-column projection. Composing "
                        + "with the equivalence between functions on Fin 2 and pairs turns each projection "
                        + "into a self-map of the finite pair type, so injectivity gives bijectivity.")),
                    Paragraph(Text(
                        "First suppose x is nonempty, and denote the input and output symbols by "
                        + "(x,y,z) and (p,q,r). Write a₁,a₂ and b₁,b₂ for the gate coordinates, and write "
                        + "c₁,c₂ for the last gate coordinates. The lifted gates on triples are "
                        + "(x,y,z) ↦ (a₁(x,y),a₂(x,y),z), "
                        + "(u,v,z) ↦ (b₁(u,z),v,b₂(u,z)), and "
                        + "(p,v,w) ↦ (p,c₁(v,w),c₂(v,w)). Their composite is injective by the "
                        + "output columns (p,q,r), hence bijective on the finite triple type. Injectivity "
                        + "of the composite makes the first lifted gate injective, hence bijective. "
                        + "Cancelling it gives a bijective composite of the other two; the same argument "
                        + "makes the second and then the third lifted gate bijective. Reassociation and "
                        + "interchange of coordinates identify these lifts with products of a, b or c "
                        + "and an identity map. Nonemptiness then gives bijectivity of a, b and c.")),
                    Paragraph(Text(
                        "Choose a fixed symbol d. For fixed y, equal values of a₁(s,y) and a₁(t,y) "
                        + "give equal p values with z = d; columns (y,z,p) force s = t. For fixed x, "
                        + "columns (x,z,p) similarly give injectivity of y ↦ a₁(x,y). Finiteness makes "
                        + "both families bijective. For fixed z, lift two proposed inputs of b₁ through "
                        + "the bijection x ↦ a₁(x,d). Equal b₁ outputs then give equal circuit rows "
                        + "by (y,z,p), so the proposed inputs coincide. For fixed first input of b₁, "
                        + "choose an a-preimage with that first output using bijectivity of a. Equal "
                        + "values as z varies give equal rows by (x,y,p). Thus b₁ is also bijective "
                        + "in each input.")),
                    Paragraph(Text(
                        "Next fix y and a desired value v of a₂. Surjectivity on columns (y,q,r) "
                        + "produces a row with these last two entries equal to c(v,d). Injectivity of c "
                        + "forces the second output of a to be v. Columns (x,q,r) give the same "
                        + "surjectivity with x fixed. Finiteness makes both one-variable maps for a₂ "
                        + "bijective. To treat the first argument of b₂ with z fixed, choose a-preimages "
                        + "of (u,d) and (v,d). If b₂(u,z) = b₂(v,z), their last two circuit outputs "
                        + "are equal, so columns (z,q,r) identify the rows and give u = v. For the "
                        + "second argument of b₂ with first argument v fixed, choose u with a₁(u,d) = v. "
                        + "Equal values b₂(v,s) and b₂(v,t) give equal q and r with y = d; columns "
                        + "(y,q,r) force s = t. Finiteness again upgrades injectivity to bijectivity.")),
                    Paragraph(Text(
                        "For the first coordinate of the last gate, fix its second input v. Choose w "
                        + "with b₂(w,d) = v, "
                        + "and a-preimages of (w,s) and (w,t). The associated circuit rows have "
                        + "the same z = d and the same p. Equality of c₁(s,v) and c₁(t,v) then lets "
                        + "columns (z,p,q) identify those rows, giving s = t. To fix the first input v, choose an "
                        + "a-preimage of (d,v), then choose inputs of the bijection z ↦ b₂(d,z) "
                        + "realizing any proposed pair s,t. Equality of c₁(v,s) and c₁(v,t) gives "
                        + "equal rows by (x,y,q), so s = t. Thus c₁ is bijective in each input by finiteness.")),
                    Paragraph(Text(
                        "For c₂ with second input v fixed, again choose w with b₂(w,d) = v "
                        + "and a-preimages of (w,s) and (w,t). The resulting rows have equal z and p; "
                        + "if c₂(s,v) = c₂(t,v), columns (z,p,r) identify the rows and force s = t. "
                        + "With first input v fixed, choose an a-preimage of (d,v), and use the "
                        + "bijection z ↦ b₂(d,z) to realize s and t. Equality of c₂(v,s) and c₂(v,t) "
                        + "then identifies the rows by (x,y,r), again forcing s = t. Finiteness makes "
                        + "both one-variable maps bijective.")),
                    Paragraph(Text(
                        "The two-column criterion now applies to a, b and c, since each gate is "
                        + "bijective and both its coordinates are bijective in either input. This proves "
                        + "the three required strength-two properties. If x is empty, the row type "
                        + "x × x and the target type Fin 2 → x are both empty, so every two-column "
                        + "projection is bijective. This gives the same conclusion in the remaining case."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pozsgay-wanless-2024-nonlinear-perfect-tensor-factors"),
                    ResolutionKind.Proved)))));

    private static Formula ArrayFormula()
    {
        Formula selection = All("cols", Arrow(FinOf(X("s")), FinOf(X("c"))),
            Imp(At(Qualified("Function", "Injective"), X("cols")),
                At(Qualified("Function", "Bijective"),
                    LambdaOf("t", X("r"), LambdaOf("i", FinOf(X("s")),
                        At(X("rows"), X("t"), At(X("cols"), X("i"))))))));
        return All("r", TypeAt("v"), All("x", TypeAt("u"),
            Instances([At(Qualified("Fintype"), X("r")), At(Qualified("Fintype"), X("x"))],
                All("c", Naturals(), All("rows", Arrow(X("r"), Arrow(FinOf(X("c")), X("x"))),
                    All("s", Naturals(), Equivalence(LocalCall("IsIndexOneOA", X("rows"), X("s")), selection)))))));
    }

    private static Formula GateFormula() => All("x", TypeAt("u"),
        All("f", GateType(), All("t", PairType(),
            Equal(Typed(LocalCall("gateGraph", X("f"), X("t")), Arrow(FinOf(D(4)), X("x"))),
                Vector(First(X("t")), Second(X("t")),
                    First(At(X("f"), X("t"))), Second(At(X("f"), X("t"))))))));

    private static Formula CircuitFormula() => All("x", TypeAt("u"),
        All("a", GateType(), All("b", GateType(), All("c", GateType(),
            All("t", TripleType(),
                Equal(Typed(LocalCall("circuit", X("a"), X("b"), X("c"), X("t")), TripleType()),
                    Let("ab", PairType(), At(X("a"), Pair(First(X("t")), First(Second(X("t"))))),
                        Let("pc", PairType(), At(X("b"), Pair(First(X("ab")), Second(Second(X("t"))))),
                            Let("qr", PairType(), At(X("c"), Pair(Second(X("ab")), Second(X("pc")))),
                                Pair(First(X("pc")), Pair(First(X("qr")), Second(X("qr")))))))))))));

    private static Formula CircuitGraphFormula()
    {
        Formula output = LocalCall("circuit", X("a"), X("b"), X("c"), X("t"));
        return All("x", TypeAt("u"), All("a", GateType(), All("b", GateType(), All("c", GateType(),
            All("t", TripleType(),
                Equal(Typed(LocalCall("circuitGraph", X("a"), X("b"), X("c"), X("t")),
                        Arrow(FinOf(D(6)), X("x"))),
                    Vector(First(X("t")), First(Second(X("t"))), Second(Second(X("t"))),
                        First(output), First(Second(output)), Second(Second(output)))))))));
    }

    private static Formula FactorizationStatement()
    {
        Formula hypothesis = LocalCall("IsIndexOneOA", LocalCall("circuitGraph", X("a"), X("b"), X("c")), D(3));
        Formula conclusion = And(LocalCall("IsIndexOneOA", LocalCall("gateGraph", X("a")), D(2)),
            And(LocalCall("IsIndexOneOA", LocalCall("gateGraph", X("b")), D(2)),
                LocalCall("IsIndexOneOA", LocalCall("gateGraph", X("c")), D(2))));
        return All("x", TypeAt("u"),
            Instances([At(Qualified("Fintype"), X("x"))],
                All("a", GateType(), All("b", GateType(), All("c", GateType(), Imp(hypothesis, conclusion))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Local(string name) => Qualified("ClassicalPerfectTensorFactorization", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula TypeAt(string level) => new Formula.Subscript(Qualified("Type"), X(level));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Product(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Times, Sp, Parenthesized(right));
    private static Formula PairType() => Product(X("x"), X("x"));
    private static Formula TripleType() => Product(X("x"), PairType());
    private static Formula GateType() => Arrow(PairType(), PairType());
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula First(Formula value) => Seq(Parenthesized(value), Dot, D(1));
    private static Formula Second(Formula value) => Seq(Parenthesized(value), Dot, D(2));
    private static Formula Vector(params Formula[] entries)
    {
        var items = new System.Collections.Generic.List<Formula> { Bang, OpenBracket };
        foreach (var entry in entries)
        {
            if (items.Count > 2) { items.Add(Comma); items.Add(Sp); }
            items.Add(entry);
        }
        items.Add(CloseBracket);
        return Seq([.. items]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instances(Formula[] types, Formula body)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var type in types)
        {
            items.Add(OpenBracket); items.Add(type); items.Add(CloseBracket); items.Add(Sp);
        }
        items.Add(Comma); items.Add(Sp); items.Add(Parenthesized(body));
        return Seq([.. items]);
    }

    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(X(name), type), Sp, Eq, Sp, value, Semi, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
