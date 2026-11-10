using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class SahasrabudheEvenAdditiveComplexityMorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/sahasrabudhe2015constantadditive");
    private const string Question = "Section 5, printed p. 7: “Can a construction of this form be generalized to give constructions of words with fixed even complexity?”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite morphism of a word containing every finite source word cannot have positive constant even additive complexity.",
        H("A parity obstruction for universal-input morphisms"),
        Blocks(
            Paragraph(Text("Sahasrabudhe's question concerns concatenating all finite words and then applying a finite morphism. Here the source alphabet is any finite nonempty type, every finite source list occurs contiguously, and the output consists of integer letters. Empty images are allowed; the cumulative boundaries must be unbounded. The conclusion concerns this construction and does not exclude other words of constant even additive complexity.")),
            Node("UniversalInput", "Every finite source word occurs", UniversalFormula(),
                "Section 5, printed p. 7: “Indeed, enumerate all words of finite length on the alphabet {0, . . . , n}, and form an infinite word w by concatenating all of the finite words in the order specified by the enumeration.” The predicate retains the resulting occurrence property: each finite list appears at a natural starting position. List.ofFn converts the length-indexed wordFactor to a list. Indices start at zero, including the empty list.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsMorphicImage", "The infinite concatenated output", MorphicFormula(),
                "Section 5, printed p. 7: “Then apply the morphism defined by” precedes the images 0 ↦ (0)(2n), 1 ↦ (1)(2n − 1), …, n ↦ (n)(n). For an arbitrary map from source letters to finite integer lists, b records the cumulative lengths, begins at zero, is monotone and unbounded, and each output segment agrees with the corresponding codeword. A zero-length image contributes no letters.",
                AssessedProvenance.FromLiterature(Source)),
            Node("factorSum", "Sum of a contiguous factor", FactorSumFormula(),
                "Section 2, printed p. 1: “A block b of a word w is a sequence of consecutive elements of w, that is b = wₖ ··· wₖ′ for k ≤ k′.” “For a block b = wₖ ··· wₖ′ of w, we define Σb := ∑ᵢ₌ₖᵏ′ wᵢ.” The displayed sum uses j : Fin n and starts at i, so it contains exactly n terms. The value of j in the addition is its natural-number value.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sumSet", "All sums at a fixed length", SumSetFormula(),
                "Section 2, printed p. 2: “The additive complexity of an infinite word w over a finite set of integers is the function ρ⁺(w, n) that counts the number of distinct sums obtained by summing n consecutive symbols of w.” The set ranges over every natural starting position; equal sums are represented once.",
                AssessedProvenance.FromLiterature(Source)),
            Node("additiveComplexity", "Number of distinct sums", ComplexityFormula(),
                "Section 2, printed p. 2: “The additive complexity of an infinite word w over a finite set of integers is the function ρ⁺(w, n) that counts the number of distinct sums obtained by summing n consecutive symbols of w.” Set.ncard gives this cardinality for finite sets. Its value on an infinite set is zero; the contradictory positive constant assumption in the proof ensures finiteness whenever the parity argument uses it. Only positive lengths enter the conclusion.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The finite-morphism construction question", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                Question + " The proposition answers the question negatively for every finite nonempty source alphabet and every universal source word. The map assigns a finite integer list to each letter. Its infinite output cannot have 2k distinct length-n sums for all positive n with k positive. Source indices are translated to zero-based natural indices, with no change in factor lengths or counts.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "No positive constant even complexity", Disp(ClaimBody()),
                "If all positive-length sum counts had one positive constant value, equal-length complete images would have equal sums: otherwise powers of two such images give too many distinct sums at a common length. The semigroup generated by codeword lengths contains every sufficiently large multiple of their gcd. Choose such a length n large enough to bracket each length-n factor by codeword boundaries and pad the bracket to length 2n. A doubled source word supplies both the factor and its complement in a cyclic rotation of this complete image. The length-n sum set is therefore invariant under reflection about the sum of a complete image of length n. That central sum occurs, and the other sums pair off, giving an odd count and a contradiction. Unbounded boundaries handle empty codewords in the same argument.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sahas2015"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("sahas-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Arrow(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Len(Formula w) => Call("List.length", w);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Parameters(Formula alpha, Formula w, Formula phi, Formula y, Formula body) =>
        All(alpha, Named("Type"), All(w, Fn(Nats(), alpha),
            All(phi, Fn(alpha, Call("List", Ints())), All(y, Fn(Nats(), Ints()), body))));

    private static Formula UniversalFormula()
    {
        Formula a = Alpha, w = F.Id("w"), u = F.Id("u"), i = F.Id("i");
        Formula body = All(u, Call("List", a), Some(i, Nats(),
            Equal(Call("List.ofFn", Call("wordFactor", w, Len(u), i)), u)));
        return Disp(All(a, Named("Type"), All(w, Fn(Nats(), a),
            Equal(Call("UniversalInput", w), Parenthesized(body)))));
    }

    private static Formula MorphicFormula()
    {
        Formula a = Alpha, w = F.Id("w"), phi = Phi, y = F.Id("y"), b = F.Id("b");
        Formula i = F.Id("i"), j = F.Id("j"), h = F.Id("h"), n = F.Id("N");
        Formula code = new Formula.Apply(phi, [new Formula.Apply(w, [i])]);
        Formula bound = Less(j, Len(code));
        Formula step = All(i, Nats(), Equal(new Formula.Apply(b, [Add(i, D(1))]),
            Add(new Formula.Apply(b, [i]), Len(code))));
        Formula infinite = All(n, Nats(), Some(i, Nats(), Less(n, new Formula.Apply(b, [i]))));
        Formula letters = All(i, Nats(), All(j, Nats(), All(h, bound,
            Equal(new Formula.Apply(y, [Add(new Formula.Apply(b, [i]), j)]),
                Call("List.get", code, Seq(Langle, Sp, j, Comma, Sp, h, Rangle))))));
        Formula body = Some(b, Fn(Nats(), Nats()),
            And(Equal(new Formula.Apply(b, [D(0)]), D(0)),
                And(Call("Monotone", b), And(step, And(infinite, letters)))));
        return Disp(Parameters(a, w, phi, y,
            Equal(Call("IsMorphicImage", w, phi, y), Parenthesized(body))));
    }

    private static Formula FactorSumFormula()
    {
        Formula y = F.Id("y"), n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(j, Colon, Sp, Call("Fin", n))), Sp,
            new Formula.Apply(y, [Add(i, Call("val", j))]));
        return Disp(All(y, Fn(Nats(), Ints()), All(n, Nats(), All(i, Nats(),
            Equal(Call("factorSum", y, n, i), sum)))));
    }

    private static Formula SumSetFormula()
    {
        Formula y = F.Id("y"), n = F.Id("n"), z = F.Id("z"), i = F.Id("i");
        Formula set = Seq(OpenBrace, z, Colon, Sp, Ints(), Sp, Bar, Sp,
            Some(i, Nats(), Equal(Call("factorSum", y, n, i), z)), CloseBrace);
        return Disp(All(y, Fn(Nats(), Ints()), All(n, Nats(), Equal(Call("sumSet", y, n), set))));
    }

    private static Formula ComplexityFormula()
    {
        Formula y = F.Id("y"), n = F.Id("n");
        return Disp(All(y, Fn(Nats(), Ints()), All(n, Nats(),
            Equal(Call("additiveComplexity", y, n), Call("Set.ncard", Call("sumSet", y, n))))));
    }

    private static Formula ClaimBody()
    {
        Formula a = Alpha, w = F.Id("w"), phi = Phi, y = F.Id("y"), k = F.Id("k"), n = F.Id("n");
        Formula counts = All(n, Nats(), Arrow(Less(D(0), n),
            Equal(Call("additiveComplexity", y, n), new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, k))));
        Formula impossible = Seq(Neg, Sp, Parenthesized(Some(k, Nats(), And(Less(D(0), k), counts))));
        Formula body = All(w, Fn(Nats(), a), All(phi, Fn(a, Call("List", Ints())),
            All(y, Fn(Nats(), Ints()), Arrow(Call("UniversalInput", w),
                Arrow(Call("IsMorphicImage", w, phi, y), impossible)))));
        return All(a, Named("Type"), Seq(
            OpenBracket, Call("Fintype", a), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", a), CloseBracket, Comma, Sp, body));
    }
}
