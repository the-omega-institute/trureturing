using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class NativeProtocolGraftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stop-aware composition of the original sixteen-bit native protocols.",
        H("Native protocol composition and original-record projection"),
        Blocks(Describe.Lean(DescribeId.Create("original-native-projection"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_native_projection"),
            H("Every original path retains its matrix, archive and resource semantics"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
            Blocks(
                Paragraph(Text("The carrier Basis is the set of all functions from Fin 16 to Bool, with shifted sites 0 through 15 representing the original sites -1 through 14. All operators are full matrices on these 65536 basis words. The root Omega is the computational word with ones at shifted positions 0, 4 and 8. No factorization of the 2584-dimensional legal subspace is used.")),
                Paragraph(Text("The menu is that of V88 definitions 23.1, 23.2 and 28.1. It uses the actual fourteen golden matrices K at addresses 0 through 13: Q is t times the zero-number projection plus t squared times the number projection plus beta cubed times bit flip; P is the product of neighboring number projections plus the product of their complements times Q; K is zeta times identity plus zeta times (zeta minus one) times P. Here phi=(1+sqrt(5))/2, t=phi inverse, beta=sqrt(t), and zeta=exp(3 pi i/5). An inverse call is interpreted as nine forward calls and costs nine. A forward call costs one.")),
                Paragraph(Text("A finite native tree has gate nodes, finite complete diagonal measurement nodes and labeled leaves. A measurement is specified by a function from Basis to Fin n: outcome o has the diagonal projector whose entries are one exactly on the fiber of o. Surjectivity is unnecessary, so zero projectors and their full successor trees remain. Feedback can depend on the whole acquired path. Leaf labels distinguish active cuts from absorbed stops; each stop has its failure, refusal, early or normal kind and its own identifying code.")),
                Paragraph(Text("For prefix T, Continuations(T) means the full function type Path(T) to Fin 2 to Tree(Stop). RecordEvent(T) means all Boolean predicates on the tuple of a natural program identifier, an original Path(T), an optional Fin 2 read and a Stop, together with a terminal Basis word. For such a continuation table C, E(p) denotes extension(T,C,p). At an active leaf E first reads original bit b1, at shifted index 2, and then executes C(p,j). At an absorbed leaf E is the single original stopped leaf: its operator is identity, its archive is empty, its added cost is zero and its read tag is none. CutLaw states these two cases, including each active read tag, diagonal projector, archive entry and terminal stop label.")),
                Paragraph(Text("G is graft(T,E). Each G path has a unique split into the original path p and an added path q of E(p), with inverse attach(T,E,p,q). The original-record projection keeps the original program pi, the full original path p, the optional original read j, the final stop and every terminal basis word z. Original path identities are retained even when two paths have equal labels or zero mass. Only the added path q is summed out. The event e is any Boolean predicate on this retained record and z.")),
                Paragraph(Text("Op denotes the chronological branch matrix; Ar is the complete gate-and-report archive; c is the expanded forward-call cost; L is its maximum over every syntactic terminal path. Mass uses normSq of Op applied to the same fixed Omega. The first equality is a raw finite Born-mass pushforward. It does not divide by success probability or erase records physically. The second equality includes every zero, failing and stopped path; it allows different continuation costs at different original leaves.")),
                Paragraph(Text("The path bijection and matrix factorization follow by induction through every original gate and measurement node. Reindexing the complete terminal sum by that bijection gives the event equality. The same induction concatenates archives and adds expanded costs. Taking the maximum over the finite, nonempty continuation fibers gives the exact whole-tree resource equality.")),
                Paragraph(Text("This composition theorem does not establish total Born-mass normalization, arithmetic integrality or nonphysical-conjugate estimates for the actual native gates. It does not construct a Petz compiler, compute the actual chi reference, or prove either numerical obstruction or resource lower bound. Those conclusions require their respective native arithmetic and reference-state bridges. No protection of the complement of b1, auxiliary preparation, reset, new controlled operation or postselection is assumed."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-event-arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_arithmetic"),
                H("Integral raw event masses exclude both reference-comparison values"),
                StatementSource.FromAuthor(ArithmeticStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
                Blocks(
                    Paragraph(Text("For every type L of terminal labels, every finite full-menu native tree T and every Boolean event e on its complete terminal path and terminal sixteen-bit word, the raw mass p=eventMass(T,e) is an algebraic integer over the ordinary integers. All fourteen actual gate addresses, deterministic feedback, complete diagonal zero-one measurements, zero outcomes, stops and expanded inverse calls are included. The input is the same fixed computational root Omega; no arbitrary input vector or external probability weights occur.")),
                    Paragraph(Text("The scalars t, beta and zeta of the actual matrices are algebraic integers: rational-angle exponential and cosine integrality give zeta and t, and beta squared equals t. Every number projection and bit flip has integer entries. Finite matrix addition, multiplication and powers therefore preserve entrywise integrality. Induction through the actual tree gives integral branch-matrix entries. Applying the fixed root, multiplying each amplitude by its physical complex conjugate and summing the selected raw events preserve integrality. The real event mass is reflected from its injective complex embedding. No success normalization is performed.")),
                    Paragraph(Text("Set q=(13-5 sqrt(5))/22 and w=(9 sqrt(5)-19)/22. In the existing quadratic golden field with generator phi, these are the images of coordinate pairs (9/11,-5/11) and (-14/11,9/11). Their field norms are respectively 1/11 and -1/11. Integrality would force an integer field norm; both rational values fail that condition. Consequently p differs from both q and w. This argument only needs absolute algebraic integrality of p and does not assert that p lies in the quadratic field.")),
                    Paragraph(Text("These exclusions apply directly to any original-record event formed by the stop-aware graft above. They do not establish that the actual chi preparation and its faithful-support Petz pullback have ideal masses q and w. That realization bridge, the quadratic-field membership of general native events, the whole-tree nonphysical-conjugate estimate and the factor-eleven resource and total-variation bounds require further results. Total Born-mass normalization and the equality of the ninth gate power with its inverse are not used or proved here."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula a, Formula op, Formula b) =>
        Seq(Open, a, Sp, op, Sp, b, Close);
    private static Formula And(params Formula[] xs) =>
        xs.Aggregate((a,b) => Rel(a,Land,b));
    private static Formula FiniteSum(Formula i, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, set), Sp, term);
    private static Formula ArithmeticStatement()
    {
        Formula L = F.Id("L"), T = F.Id("T"), e = F.Id("e");
        Formula p = Call("eventMass", T, e);
        Formula q = Seq(Frac, Grp(D(13), Minus, D(5), Sqrt, Grp(D(5))), Grp(D(22)));
        Formula w = Seq(Frac, Grp(D(9), Sqrt, Grp(D(5)), Minus, D(19)), Grp(D(22)));
        Formula neq(Formula a, Formula b) =>
            new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
        return Disp(All("L", Call("Type"), All("T", Call("Tree", L),
            All("e", Call("Events", T), And(Call("IsIntegral", Call("Int"), p),
                neq(p, q), neq(p, w)))));
    }
    private static Formula Statement()
    {
        Formula T = F.Id("T"), C = F.Id("C"), pi = F.Id("pi"), e = F.Id("e");
        Formula p = F.Id("p"), q = F.Id("q"), z = F.Id("z");
        Formula E = Call("extension", T, C), G = Call("graft", T, E);
        Formula Ep = Call("Apply", E, p), path = Call("Path", T);
        Formula tag = Call("readTag", Call("label", T, p), Call("Apply", C, p), q);
        Formula record = Call("Record", pi, p, tag, Call("label", Ep, q));
        Formula product = Call("MatMul", Call("Op", Ep, q), Call("Op", T, p));
        Formula mass = Call("normSq", Call("Apply", Call("mulVec", product, Call("omegaZero")), z));
        Formula sum = FiniteSum(p, path, FiniteSum(q, Call("Path", Ep),
            FiniteSum(z, Call("Basis"), IfThenElse(Call("Apply", e, record, z), mass, D(0)))));
        Formula r = Call("attach", T, E, p, q);
        Formula semantics = All("p", path, All("q", Call("Path", Ep), And(
            Rel(Call("Op", G, r), Eq, product),
            Rel(Call("Ar", G, r), Eq, Call("Append", Call("Ar", T, p), Call("Ar", Ep, q))),
            Rel(Call("c", G, r), Eq, Rel(Call("c", T, p), Plus, Call("c", Ep, q))),
            Rel(Call("label", G, r), Eq, Call("label", Ep, q)))));
        Formula bound = Rel(Call("L", G), Eq,
            Seq(Operatorname, Grp(F.Id("sup")), Underscore,
                Grp(p, Sp, InMacro, Sp, path), Sp,
                Rel(Call("c", T, p), Plus, Call("L", Ep))));
        Formula law = And(Rel(Call("projectedMass", T, C, pi, e), Eq, sum), bound,
            All("p", path, Call("CutLaw", Call("label", T, p), Call("Apply", C, p))), semantics);
        return Disp(All("T", Call("Tree", Call("Cut")),
            All("C", Call("Continuations", T), All("pi", Call("Nat"),
            All("e", Call("RecordEvent", T), law)))));
    }
}
