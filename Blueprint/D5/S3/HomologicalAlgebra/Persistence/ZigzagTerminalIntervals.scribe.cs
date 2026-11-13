using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class ZigzagTerminalIntervalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/carlsson2008zigzag");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite right-streamlined zigzags split into terminal intervals with their actual right-filtration multiplicities.",
        H("Terminal intervals on the actual oriented path"),
        Blocks(Describe.Lean(
            DescribeId.Create("terminal-interval-decomposition"),
            DeclarationHandle.Create(Prefix + "exists_terminal_interval_decomposition"),
            H("Streamlined interval decomposition and exact birth counts"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "The universes u and v are independent. K is an arbitrary field in Type u, "
                    + "and D is the native Zigzag with vertex modules in Type v and an actual "
                    + "forward or backward linear arrow at every adjacent pair. Only indices below "
                    + "m require finite-dimensional spaces. Every active forward arrow is injective; "
                    + "every active backward arrow is surjective. No basis, barcode, splitting or "
                    + "natural isomorphism is supplied as a hypothesis.")),
                Paragraph(Text(
                    "For m=n+1, the source is exactly Paths(Vertex D n), with the original Edge D n. "
                    + "The input is postcomposed with ModuleCat.uliftFunctor into ModuleCat at "
                    + "max u v. terminalInterval D n b uses lifted K at vertices b through n, zero "
                    + "before b, identity on supported generating arrows and zero otherwise. "
                    + "intervalSum is the actual finite categorical biproduct. Fin r records "
                    + "occurrences, so repeated births retain their full multiplicities.")),
                Paragraph(Text(
                    "R(D,n,i) below is terminalFiltrationLayer, read from the actual native "
                    + "rightFiltration, including its zero and whole-space endpoints and repeated "
                    + "layers. inclusion(D,n,i) is the proved inclusion from layer i into layer i+1. "
                    + "The quotient is by its actual range inside the next layer. beta(D,n,i) is "
                    + "birthOrder: start with 0, append the new vertex at a forward arrow and "
                    + "prepend it at a backward arrow. Every factor dimension, including zero, "
                    + "equals the corresponding occurrence count. cardBirthFibre(birth,b) is "
                    + "the cardinality of the subtype of j in Fin r with birth j=b.")),
                Paragraph(Text(
                    "The construction extends compatible coordinates through an injective arrow "
                    + "using a complement of its image, and through a surjective arrow using a "
                    + "linear section and its kernel. Existing Mathlib complement, section and "
                    + "finite-basis APIs provide these ingredients. Generating-arrow squares "
                    + "extend to all actual paths; pointwise linear equivalences give the natural "
                    + "isomorphism. Rank-nullity and the proved quotient-dimension formula connect "
                    + "the native filtration recurrence to the birth fibres. ZigzagNaturalLift "
                    + "provides the native data, filtration and source-category interfaces; its "
                    + "endomorphism reconstruction is not repeated.")),
                Paragraph(Text(
                    "At m=0, EmptyVertex has no objects, and the conclusion is an actual natural "
                    + "isomorphism from its unique diagram to the empty biproduct. Native n=0 "
                    + "instead means one vertex. All-zero spaces, repeated intervals, arbitrary "
                    + "characteristic and every direction word remain in scope; inactive tail "
                    + "data are unconstrained. The result asserts existence, without canonical "
                    + "choices or a unique isomorphism. Early-death intervals and unrestricted "
                    + "type-A classification are outside this statement.")),
                Paragraph(Text(
                    "The positive-length specification is Carlsson and de Silva, Zigzag "
                    + "Persistence, arXiv:0812.0197v1, Theorem 3.19 in Section 3, with the birth "
                    + "ordering of Definition 3.6. Paper vertices 1 through m correspond to "
                    + "native vertices 0 through m-1. The empty source is the explicit vacuous "
                    + "extension. This is a formalization of a known theorem, without a claim "
                    + "of mathematical novelty or an open-problem resolution."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula ResultFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), k = F.Id("K"), d = F.Id("D");
        Formula m = F.Id("m"), n = F.Id("n"), r = F.Id("r"), b = F.Id("birth"), i = F.Id("i");
        Formula length = Call("succ", n);
        Formula birthType = new Formula.TypeArrow(Call("Fin", r), Call("Fin", length));
        Formula quotient = Call("Quotient", Call("R", d, n, Call("succ", i)),
            Call("range", Call("inclusion", d, n, i)));
        Formula counts = All([Bound("i", Call("Fin", length))],
            Eq(Call("cardBirthFibre", b, Call("beta", d, n, i)), Call("finrank", k, quotient)));
        Formula positive = All([Bound("n", Call("Nat"))], Imp(Eq(m, length),
            Exists([Bound("r", Call("Nat")),
                Bound("birth", birthType)],
                And(Call("NonemptyNaturalIso", Call("liftedDiagram", d, n, u, v),
                    Call("intervalSum", d, n, r, b, u, v)), counts))));
        Formula empty = Imp(Eq(m, Call("zero")),
            Call("NonemptyNaturalIso", Call("emptyDiagram", k, u, v), Call("emptyIntervalSum", k, u, v)));
        Formula a = F.Id("a"), f = F.Id("f"), g = F.Id("g");
        Formula current = Call("space", d, a), next = Call("space", d, Call("succ", a));
        Formula finite = All([Bound("a", Call("Nat"))],
            Imp(new Formula.Relation(a, FormulaRelationOperator.LessThan, m),
                Call("FiniteDimensional", k, current)));
        Formula forward = All([Bound("f", Call("LinearMap", k, current, next))],
            Imp(Eq(Call("arrow", d, a), Call("inl", f)), Call("Injective", f)));
        Formula backward = All([Bound("g", Call("LinearMap", k, next, current))],
            Imp(Eq(Call("arrow", d, a), Call("inr", g)), Call("Surjective", g)));
        Formula streamlined = All([Bound("a", Call("Nat"))],
            Imp(new Formula.Relation(Call("succ", a), FormulaRelationOperator.LessThan, m),
                And(forward, backward)));
        Formula hypotheses = And(Call("Field", k), And(finite, streamlined));
        return Disp(All([Bound("u", Call("Universe")), Bound("v", Call("Universe")),
            Bound("K", Call("Type", u)), Bound("D", Call("Zigzag", k, v)), Bound("m", Call("Nat"))],
            Imp(hypotheses, And(empty, positive))));
    }
}
