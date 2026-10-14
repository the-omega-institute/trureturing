using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class FiniteWordReachabilityDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Observer/LinearMemory/FiniteWordReachability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered endomorphism words reach the whole reachable seed span by its rank gap.",
        H("Finite word reachability"),
        Blocks(
            Paragraph(Text("Let K be a division ring, E a left K-module with an additive commutative group, "
                + "I any alphabet, A an I-indexed family of K-linear endomorphisms, and U a seed submodule. "
                + "The three type universes are independent. The alphabet may be empty or infinite. "
                + "For a list w, its action is the product of the list mapped through A. Multiplication "
                + "of endomorphisms is composition: the head acts after the tail, and the empty word acts as identity.")),
            Describe.Lean(DescribeId.Create("bounded-word-span"),
                DeclarationHandle.Create(Root + "boundedSpan"), H("Words through a finite horizon"),
                StatementSource.FromAuthor(Parameters(Seq(
                    Forall, Sp, F.Id("n"), Colon, Sp, F.Id("N"), Comma, Sp,
                    Call("boundedSpan", F.Id("A"), F.Id("U"), F.Id("n")), Sp, Eq, Sp,
                    WordSpan(true)), false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The length condition includes every shorter word and the empty word. "
                    + "The span permits arbitrary finite linear combinations of word images from U."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reachable-word-span"),
                DeclarationHandle.Create(Root + "reachableSpan"), H("All finite words"),
                StatementSource.FromAuthor(Parameters(Seq(
                    Call("reachableSpan", F.Id("A"), F.Id("U")), Sp, Eq, Sp, WordSpan(false)), false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the smallest submodule containing U and invariant under every A(i). "
                    + "The ordered-word induction in the proof establishes the closure property used below."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bounded-span-equals-reachable"),
                DeclarationHandle.Create(Root + "bounded_span_eq_reachable"),
                H("The reachable rank gap bounds the horizon"),
                StatementSource.FromAuthor(Parameters(Seq(
                    Call("boundedSpan", F.Id("A"), F.Id("U"),
                        Seq(Call("finrank", F.Id("K"), Call("reachableSpan", F.Id("A"), F.Id("U"))),
                            Sp, Minus, Sp, Call("finrank", F.Id("K"), F.Id("U")))),
                    Sp, Eq, Sp, Call("reachableSpan", F.Id("A"), F.Id("U"))), true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume E is finite dimensional. Write R for the full reachable span and "
                        + "b = dim(R) - dim(U). Then W(b) = R, so every ordered word image of every seed vector "
                        + "lies in W(b). This is stabilization by b; b need not be the first stable index. "
                        + "Neither commutation, positive seed rank, invariance, nor a pre-existing plateau is assumed. "
                        + "The zero seed and zero ambient space are included.")),
                    Paragraph(Text("For F(S) = S + sup over i of A(i)S, induction identifies F iterated n times "
                        + "on U with W(n). These iterates increase inside R. The public bounded_monotone_has_equal_step "
                        + "theorem in FiniteSequentialWordCertificate supplies an equal-rank consecutive pair by b. "
                        + "Inclusion and equal finite rank turn that pair into an F-fixed submodule. Ordered-word "
                        + "induction puts every finite word image inside it, identifying it with R. Fixed-point "
                        + "iteration reaches the same space at b. Since R is contained in E, monotonicity also "
                        + "gives W(dim(E) - dim(U)) = R.")),
                    Paragraph(Text("The application is the finite-horizon step of section 349.2, Lemma 349.1, "
                        + "equations 349.8 through 349.12 of RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY. "
                        + "Take the scalar field to be the complex numbers and E the coordinate space on Fin(d), with "
                        + "dimension d counting the full persistent carrier. Set A(i) = mulVecLin(K(i)) "
                        + "and U = range(tau), where tau is the positive initial operator. A finite Kraus family "
                        + "defines Phi(X) = sum over i of K(i) X K(i)*; the empty family and zero CP map are allowed. "
                        + "At an interior parameter with strictly positive branch weights, rescaling Kraus operators "
                        + "by their nonzero square-root weights preserves the word-image spans. This theorem supplies "
                        + "the horizon b for that algebraic span.")),
                    Paragraph(Text("To infer that the positive sum of Phi iterated k times on tau, for k from zero "
                        + "through b, is faithful on R still requires the matrix-support identities for a Kraus image "
                        + "and for a positive sum, and the restriction-to-support faithfulness theorem. These downstream "
                        + "Lean interfaces remain unproved here; no D5 importer currently supplies this application. "
                        + "If tau is zero, the reachable carrier is zero. Every persistent classical register, retained "
                        + "seed, program counter, clock value, archive and returning environment belongs in the carrier "
                        + "dimension. The algebraic horizon asserts neither a preparation procedure, CP growth, "
                        + "physical resource savings nor literature novelty."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Parameters(Formula body, bool finite)
    {
        Formula k = F.Id("K"), e = F.Id("E"), i = F.Id("I");
        var items = new List<Formula> {
            Forall, Sp, k, Comma, Sp, e, Comma, Sp, i, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("DivisionRing", k), CloseBracket, Sp,
            OpenBracket, Call("AddCommGroup", e), CloseBracket, Sp,
            OpenBracket, Call("Module", k, e), CloseBracket, Sp };
        if (finite) items.AddRange([OpenBracket, Call("FiniteDimensional", k, e), CloseBracket, Sp]);
        items.AddRange([Forall, Sp, F.Id("A"), Colon, Sp, i, Sp, To, Sp, Call("End", k, e), Comma, Sp,
            F.Id("U"), Colon, Sp, Call("Submodule", k, e), Comma, Sp, body]);
        return Disp(Seq([.. items]));
    }

    private static Formula WordSpan(bool bounded)
    {
        var items = new List<Formula> { OpenBrace, F.Id("x"), Sp, Mid, Sp,
            Exists, Sp, F.Id("w"), Colon, Sp, Call("List", F.Id("I")), Comma, Sp };
        if (bounded) items.AddRange([Call("length", F.Id("w")), Sp, Leq, Sp, F.Id("n"), Sp, Land, Sp]);
        items.AddRange([Exists, Sp, F.Id("z"), Sp, InMacro, Sp, F.Id("U"), Comma, Sp,
            F.Id("x"), Sp, Eq, Sp, Call("apply", Call("prod", Call("map", F.Id("A"), F.Id("w"))),
                F.Id("z")), CloseBrace]);
        return Call("span", F.Id("K"), Seq([.. items]));
    }
}
