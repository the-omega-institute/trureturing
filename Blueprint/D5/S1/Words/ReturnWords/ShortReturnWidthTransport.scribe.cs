using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class ShortReturnWidthTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ReturnWords/ShortReturnWidthTransport.";
    private static readonly Formula A = F.Id("a"), B = F.Id("b"), N = F.Id("n"), P = F.Id("p");
    private static readonly Formula G = F.Id("g"), D = F.Id("d"), W = F.Id("w");
    private static readonly Formula K = F.Id("k"), U = F.Id("u"), I = F.Id("i");
    private static readonly Formula Delta = F.Id("delta"), Ell = F.Id("ell");
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula StartsType => new Formula.TypeArrow(NatType, RealType);
    private static Formula TwiceMinusOne => Sub(Mul(Digit(2), N), Digit(1));
    private static Formula Bound => Mul(Mul(P, FloorDiv(N, P)), FloorDiv(TwiceMinusOne, P));
    private static Formula Sync => Call("lcm", A, B);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite interval chains, affine packing, and conditional short-return width estimates.",
        H("Finite packing and short return width transport"),
        Blocks(
            Paragraph(Text(
                "There are k+1 interval starts x(0),...,x(k). Adjacent separation accumulates "
                + "to k times the separation, including the degenerate case k=0. The affine "
                + "application separates full length-d intervals from the width-w images that "
                + "lie in the parent. Natural division is floor division, and natural subtraction "
                + "is truncated at zero.")),
            Describe.Lean(
                DescribeId.Create("finite-interval-chain-packing"),
                DeclarationHandle.Create(Prefix + "finite_interval_chain_packing"),
                H("Accumulate local separation along a finite chain"),
                StatementSource.FromAuthor(Disp(AllNat(new[] { "k" }, All(new[] { "x" }, StartsType,
                    AllReal(new[] { "delta", "ell", "u", "w" }, Imp(
                        Conj(Le(U, X(Digit(0))), Adjacent(Delta),
                            Le(Add(X(K), Ell), Add(U, W))),
                        Le(Add(Mul(K, Delta), Ell), W))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induct on m<=k to prove x(0)+m delta<=x(m). The successor step combines "
                    + "the induction inequality with the local edge at m. At m=k the two parent "
                    + "endpoint bounds give k delta+ell<=w. All real delta and ell are allowed; "
                    + "their nonnegative instances have the interval interpretation. "
                    + "This estimate is used by affine_cylinder_chain_packing."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("affine-cylinder-chain-packing"),
                DeclarationHandle.Create(Prefix + "affine_cylinder_chain_packing"),
                H("Pack affine interval images using a separate separation scale"),
                StatementSource.FromAuthor(Disp(AllNat(new[] { "k", "L" },
                    AllReal(new[] { "g", "d", "w", "u" }, All(new[] { "x" }, StartsType, Imp(
                        Conj(Lt(Digit(0), G), Le(Digit(0), W), Inside(F.Id("L")), Adjacent(D)),
                        Le(Mul(K, Mul(Pow(G, F.Id("L")), D)),
                            Mul(Sub(Digit(1), Pow(G, F.Id("L"))), W)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set q=g^L and y(i)=u+q x(i). Whole-interval inclusion supplies the parent "
                    + "bounds for y(0) and y(k)+q w; the scaled adjacent inequalities supply "
                    + "y(i)+q d<=y(i+1). The finite chain estimate gives k q d+q w<=w, hence "
                    + "k q d<=(1-q)w. For k=1 this is q d<=(1-q)w, the two-cylinder packing "
                    + "inequality. For d>=0 the separate intervals [x(i),x(i)+d] have disjoint "
                    + "interiors; inclusion is required only for the width-w images. Negative d "
                    + "is also allowed algebraically, and no contraction upper bound is needed "
                    + "here. This estimate supplies short_return_width_lower_bound_of_chain."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("short-return-synchronization-bound"),
                DeclarationHandle.Create(Prefix + "synchronized_length_le_phase_bound"),
                H("Phase divisibility bounds the synchronization length"),
                StatementSource.FromAuthor(Disp(AllNat(new[] { "a", "b", "n", "p" },
                    Imp(LengthHypotheses(), Le(Sync, Bound))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Writing a=p alpha and b=p gamma gives lcm(a,b)=p lcm(alpha,gamma). "
                    + "The quotient bounds and the Mathlib product bound give the estimate. "
                    + "Zero lengths are allowed. This arithmetic helper is used by "
                    + "short_return_width_lower_bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("short-return-contraction-antitone"),
                DeclarationHandle.Create(Prefix + "contraction_ratio_antitone"),
                H("The contraction ratio decreases with the positive scale"),
                StatementSource.FromAuthor(Disp(AllReal(new[] { "g" },
                    AllNat(new[] { "L", "M" }, Imp(
                        Conj(Lt(Digit(0), G), Lt(G, Digit(1)), Lt(Digit(0), F.Id("L")),
                            Le(F.Id("L"), F.Id("M"))),
                        Le(Ratio(F.Id("M")), Ratio(F.Id("L")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Power order and positive-denominator fraction comparison give this helper. "
                    + "Equality of scales is included. It is used by short_return_width_lower_bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("short-return-width-lower-bound"),
                DeclarationHandle.Create(Prefix + "short_return_width_lower_bound"),
                H("Arithmetic transport of a supplied packing inequality"),
                StatementSource.FromAuthor(Disp(AllNat(new[] { "a", "b", "n", "p" },
                    AllReal(new[] { "g", "d", "w" }, Imp(
                        Conj(Lt(Digit(0), G), Lt(G, Digit(1)), Le(Digit(0), D),
                            LengthHypotheses(), Lt(Digit(0), A), Lt(Digit(0), B),
                            Le(Mul(Pow(G, Sync), D), Mul(Sub(Digit(1), Pow(G, Sync)), W))),
                        Le(Mul(Ratio(Bound), D), W)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This arithmetic helper assumes packing at the actual LCM, divides by its "
                    + "positive denominator, and applies the LCM and ratio helpers. "
                    + "It is used by short_return_width_lower_bound_of_chain, which derives "
                    + "the packing premise from interval inclusion and adjacent separation."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("short-return-width-lower-bound-of-chain"),
                DeclarationHandle.Create(Prefix + "short_return_width_lower_bound_of_chain"),
                H("Transport the accumulated packing estimate to the uniform scale"),
                StatementSource.FromAuthor(Disp(AllNat(new[] { "a", "b", "n", "p", "k" },
                    AllReal(new[] { "g", "d", "w", "u" }, All(new[] { "x" }, StartsType, Imp(
                        Conj(Lt(Digit(0), G), Lt(G, Digit(1)), Le(Digit(0), D), Le(Digit(0), W),
                            LengthHypotheses(), Lt(Digit(0), A), Lt(Digit(0), B),
                            Inside(Sync), Adjacent(D)),
                        Le(Mul(Ratio(Bound), Mul(K, D)), W))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Put L=lcm(a,b) and M=p floor(n/p) floor((2n-1)/p). Applying the affine "
                        + "packing theorem derives k g^L d<=(1-g^L)w from the interval hypotheses. "
                        + "The arithmetic helpers give L<=M and decrease the ratio, yielding "
                        + "w>=k g^M d/(1-g^M). The k=1 specialization recovers the two-cylinder "
                        + "width bound. The cardinality factor retains the full chain estimate; "
                        + "no packing inequality is assumed as a premise of this chain application.")),
                    Paragraph(Text(
                        "The chain statement uses abstract intervals with positive affine orientation. "
                        + "The full guard cylinders supply separation, and the smaller images supply "
                        + "containment in the original piece."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-detecting-returns"),
                DeclarationHandle.Create(Prefix + "exists_bounded_detecting_returns"),
                H("A shortest return and a failing simple-path test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In any incoherent finite cyclic strongly connected component with n "
                        + "vertices, fix a base vertex. There is a shortest positive return "
                        + "of length at most n. Choose simple paths to and from each vertex with "
                        + "length less than n, using empty paths at the base. A positive test "
                        + "return of length at most 2n−1 has a different label word after "
                        + "synchronization with the shortest return.")),
                    Paragraph(Text(
                        "A test joins the two paths at a vertex or inserts one actual directed "
                        + "edge between them. If every nonempty test agreed with the shortest "
                        + "return, the least period of its repeated word would divide the "
                        + "lengths of those test returns. The vertex and edge tests then "
                        + "give a phase and determine the label on each edge, implying coherence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("width-at-incoherent-basepoint"),
                DeclarationHandle.Create(Prefix + "width_at_incoherent_basepoint"),
                H("Width at every basepoint of an incoherent cyclic component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a vertex of a finite cyclic strongly connected component that is incoherent "
                        + "for a single-symbol edge label. Let n be its vertex count. Assume a positive "
                        + "phase modulus p with increment one on every edge and a contraction 0 < g < 1. "
                        + "A nondegenerate guard interval has width d and a closed piece has width w. "
                        + "For every return C of length L, its map has slope (−g)^L and sends the piece "
                        + "into itself. Returns of equal length with distinct label words send the open "
                        + "guard interval to disjoint images.")),
                    Paragraph(Text("Set M equal to "),
                        Math(Bound),
                        Text(". Then w is at least "),
                        Math(Mul(Ratio(F.Id("M")), D)),
                        Text(".")),
                    Paragraph(Text(
                        "In a component of n vertices, find two actual returns at the given basepoint "
                        + "with different synchronized label words. Their positive lengths are at most "
                        + "n and 2n−1. Short paths to and from each vertex define a bounded return test. "
                        + "If every test agreed with a short reference return, the reference word’s "
                        + "least period would define a phase and a label at every edge. That would give "
                        + "coherence for the component.")),
                    Paragraph(Text(
                        "The independently supplied phase has modulus p and increases by one on every "
                        + "edge. It divides both return lengths. At their least common multiple the two "
                        + "whole guard cylinders have disjoint interiors, while the two original-piece "
                        + "images belong to the original piece. Their common slope can have either "
                        + "sign. Comparing endpoints yields the packing inequality at the least common "
                        + "multiple and hence the stated uniform bound.")),
                    Paragraph(Text(
                        "The statement takes the original piece and guard intervals, their affine "
                        + "return maps, and the separation of whole guard cylinders as premises. "
                        + "Application to Proposition 51.3 requires deriving those premises and the "
                        + "second-label phase from the original legal graph."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("legal-word-open-cylinders-disjoint"),
                DeclarationHandle.Create(Prefix + "legal_word_open_cylinders_disjoint"),
                H("Disjoint open cylinders for distinct legal words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two distinct words of the same length start in a common guard. "
                        + "Each word is legal through its own terminal guard. The image of "
                        + "the open interval of the first terminal guard under its word map is "
                        + "disjoint from the corresponding open image for the second word.")),
                    Paragraph(Text(
                        "At the first differing label, the open images lie in distinct intervals "
                        + "of the original five-branch partition. A common preceding label "
                        + "determines the next guard and acts by an injective affine map. "
                        + "Closed cylinders can share endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("width-at-original-first-piece"),
                DeclarationHandle.Create(Prefix + "width_at_original_first_piece"),
                H("Width bound using the original first-projection edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a vertex of a finite cyclic strongly connected component with "
                        + "incoherent first labels. Its first pieces have ordered endpoints. Each arrow "
                        + "satisfies the legality and whole-interval containment tests of the "
                        + "original endpoint graph. Assume a positive "
                        + "phase modulus p with increment one on each arrow. Take n to be "
                        + "the component size, d the full guard width at the base vertex, "
                        + "w the width of its first piece, and g the positive contraction "
                        + "magnitude of the original three-bit deletion.")),
                    Paragraph(Text("Set M equal to "),
                        Math(Bound),
                        Text(". Then w is at least "),
                        Math(Mul(Ratio(F.Id("M")), D)),
                        Text(".")),
                    Paragraph(Text(
                        "Edge containment gives the affine transport of each original piece "
                        + "along a full return, and the guard law makes its output word legal. "
                        + "The open-cylinder theorem supplies separation for the synchronized "
                        + "returns in the width argument. The next two results supply the phase "
                        + "from the original second-label projection and apply it jointly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-projection-phases"),
                DeclarationHandle.Create(Prefix + "singleton_projection_phases"),
                H("A singleton projection supplies a common label phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite cyclic strongly connected component projects to the original "
                        + "endpoint graph, with one fixed label on each projected arrow. If one "
                        + "projected piece is a singleton in its guard interval, there is a positive phase modulus p "
                        + "bounded by the component size. The label depends only on the phase "
                        + "at the source, and each edge advances that phase by one.")),
                    Paragraph(Text(
                        "Any return word prepends to the legal encodings of the singleton, "
                        + "preserving its guard and scalar. This is an injection because the "
                        + "same prefix has a unique deleted tail. The signed-series fiber "
                        + "classification makes the encoding fiber finite, so the injection "
                        + "is surjective. Both synchronized words must then be prefixes of "
                        + "one actual encoding and agree because they have the same length. "
                        + "Coherence supplies the bounded phase."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("paired-singleton-short-return-width"),
                DeclarationHandle.Create(Prefix + "paired_singleton_short_return_width"),
                H("The short-return width bound for a paired component with a singleton projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose a finite cyclic strongly connected component projects along "
                        + "each of its two labelings to legal original endpoint-graph edges. "
                        + "Assume first-label incoherence, ordered endpoints of the first pieces, and a "
                        + "singleton second piece in its guard interval at some vertex. "
                        + "Write n for the size of the same component in both projections. "
                        + "There is one positive modulus p at most n, with a second-label phase "
                        + "that advances by one on each edge and determines its second label.")),
                    Paragraph(Text("Set M equal to "),
                        Math(Bound),
                        Text(". At every vertex, the first-piece width is at least "),
                        Math(Mul(Ratio(F.Id("M")), D)),
                        Text(", where d is the full first guard width and g is the contraction magnitude.")),
                    Paragraph(Text(
                        "The singleton projection supplies the phase, and the first edges "
                        + "supply the legal return words, piece containment and full-cylinder "
                        + "separation. Proposition 51.3 uses these edge laws on its supplied paired "
                        + "component for any admissible endpoint set. Reachability or a particular "
                        + "endpoint color assignment is outside "
                        + "the width calculation."))),
                DescribeRole.Theorem))));

    private static Formula X(Formula i) => Call("x", i);
    private static Formula Adjacent(Formula separation) => AllNat(new[] { "i" },
        Imp(Lt(I, K), Le(Add(X(I), separation), X(Add(I, Digit(1))))));
    private static Formula Inside(Formula exponent) => AllNat(new[] { "i" }, Imp(Le(I, K),
        new Formula.Relation(
            Call("Icc", Add(U, Mul(Pow(G, exponent), X(I))),
                Add(U, Mul(Pow(G, exponent), Add(X(I), W)))),
            FormulaRelationOperator.SubsetOf, Call("Icc", U, Add(U, W)))));
    private static Formula LengthHypotheses() => Conj(Lt(Digit(0), P),
        Divides(P, A), Divides(P, B), Le(A, N), Le(B, TwiceMinusOne));
    private static Formula Ratio(Formula exponent) =>
        new Formula.Fraction(Pow(G, exponent), Sub(Digit(1), Pow(G, exponent)));
    private static Formula FloorDiv(Formula x, Formula y) =>
        Seq(Lfloor, new Formula.Fraction(x, y), Rfloor);
    private static Formula Digit(byte digit) => F.D(digit);
    private static Formula AllNat(string[] names, Formula body) => All(names, NatType, body);
    private static Formula AllReal(string[] names, Formula body) => All(names, RealType, body);
    private static Formula All(string[] names, Formula type, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(names[i]), type, body);
        return body;
    }
    private static Formula Conj(params Formula[] parts)
    {
        var body = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            body = new Formula.Logic(parts[i], FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Divides(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
}
