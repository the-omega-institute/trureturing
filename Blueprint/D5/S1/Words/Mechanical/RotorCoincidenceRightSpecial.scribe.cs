using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class RotorCoincidenceRightSpecialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Rewriting/krishnaswamirameshan2026rotor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every irrational slope greater than one, the unique right-special rotor factor of each positive length is the reversed prefix after the initial zero.",
        H("The right-special word of a rotor sequence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cutting"),
                DeclarationHandle.Create(Prefix + "cutting"),
                H("An arithmetic cutting sequence"),
                StatementSource.FromAuthor(Disp(CuttingFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The function cutting is defined for every real σ and natural m. It takes the value 3 "
                    + "exactly at indices of the form floor(kσ) + k with k a positive natural number, "
                    + "and takes the value 1 elsewhere. Here floor means the natural-valued floor, and k "
                    + "is first cast to a real number. In particular its value at m = 0 is 1. "
                    + "For irrational σ > 1, the positive indices describe the cutting sequence of "
                    + "y = σx starting at the origin, as in the v1 TeX, line 831. At the kth vertical "
                    + "crossing there have been floor(kσ) horizontal crossings and k vertical crossings; "
                    + "irrationality excludes simultaneous crossings. The index criterion therefore "
                    + "assigns 3 to vertical crossings and 1 to horizontal crossings."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rotor"),
                DeclarationHandle.Create(Prefix + "rotor"),
                H("The separator encoding"),
                StatementSource.FromAuthor(Disp(RotorFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The rotor sequence starts with 0. Its odd positions contain the separator 2, "
                    + "and each positive even position m contains cutting(σ, m / 2), with natural "
                    + "division. Thus it reads 0, 2, s₁, 2, s₂, 2, s₃, and so on. This is the "
                    + "correspondence in the v1 TeX, line 835, for irrational σ > 1. The displayed "
                    + "definition also specifies a sequence for every other real σ."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-factor"),
                DeclarationHandle.Create(Prefix + "IsFactor"),
                H("Finite factors"),
                StatementSource.FromAuthor(Disp(FactorFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A list w is a factor of a sequence R when it occurs at some natural starting "
                    + "position i: its tth entry equals R(i + t) for every t below its length. "
                    + "The variable h certifies that the list entry exists. This makes precise the "
                    + "subwords used in the v1 TeX, line 697. The definition allows an arbitrary "
                    + "natural-valued sequence and includes the empty list."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-right-special"),
                DeclarationHandle.Create(Prefix + "IsRightSpecial"),
                H("Two distinct right extensions"),
                StatementSource.FromAuthor(Disp(RightSpecialFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A list w is right-special when two distinct natural symbols a and b can "
                    + "each be appended to w to obtain a factor of R. The two extended words may "
                    + "occur at different positions. This is the right-special condition in the "
                    + "v1 TeX, line 697; no restriction to a fixed finite alphabet is imposed "
                    + "in the definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The reversed-prefix characterization"),
                StatementSource.FromAuthor(Disp(Equivalence(Op("claim"), ClaimFormula()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every irrational σ > 1 and natural n ≥ 2, a list w of length n − 1 "
                    + "is right-special precisely when it is the reversal of rotor(σ, 1), through "
                    + "rotor(σ, n − 1). This states the conjecture in the v1 TeX, line 701, "
                    + "with the right-special condition of line 697; the question is also listed "
                    + "in the Discussion, line 917. Since 0 occurs only at position zero, the "
                    + "unique factor of length n beginning with 0 is the initial prefix. "
                    + "Deleting its 0 and reversing gives exactly the list in the formula. "
                    + "The index t belongs to Fin(n − 1); Fin.val explicitly casts it to a "
                    + "natural number before adding one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Identification and uniqueness of the right-special factor"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First relate a crossing index to a floor jump. For an irrational real d > 1 "
                        + "and natural m, the existence of a positive natural k with m = floor(kd) "
                        + "is equivalent to the integer-valued floor difference "
                        + "floor((m + 1) / d) − floor(m / d) being 1. In the forward direction, "
                        + "irrationality gives m < kd < m + 1. Since 1 / d < 1, the two floors "
                        + "are k − 1 and k. Conversely, let z = floor((m + 1) / d). A jump of one "
                        + "makes z positive. Taking k = z.toNat gives m < kd ≤ m + 1, and "
                        + "irrationality makes the upper inequality strict, so the natural floor "
                        + "of kd is m.")),
                    Paragraph(Text(
                        "Set α = 1 / (σ + 1). Then 0 < α < 1 and α is irrational. Apply the "
                        + "floor-jump equivalence with d = σ + 1 and m = j + 1. The natural-floor "
                        + "identity floor(k(σ + 1)) = floor(kσ) + k identifies cutting(σ, j + 1) "
                        + "with 3 when lowerMechanicalWord(α, α, j) is true and with 1 when it "
                        + "is false. Indeed the corresponding mechanical letter is the "
                        + "integer-floor difference floor((j + 2)α) − floor((j + 1)α).")),
                    Paragraph(Text(
                        "Next construct both right extensions of the reversed mechanical prefix. "
                        + "For any finite N, irrationality keeps −qα away from integers for "
                        + "1 ≤ q ≤ N. Finite floor stability supplies ε > 0 such that subtracting "
                        + "any δ with 0 ≤ δ < ε leaves all these floors unchanged. One obtains "
                        + "this from stability at slope −α by perturbing the slope by −δ / q; "
                        + "because q ≥ 1, the perturbation has absolute value at most δ.")),
                    Paragraph(Text(
                        "For a prefix of length m and a Boolean b, use N = m + 1 and take δ = 0 "
                        + "if b is true, and δ = min(ε, 1 − α) / 2 if b is false. In either case "
                        + "0 ≤ δ < ε and δ < 1 − α. Consider the length m + 1 mechanical factor "
                        + "at position zero with intercept −(m + 1)α − δ. For its first m letters, "
                        + "the unchanged negative floors and the identity "
                        + "floor(−qα) = −floor(qα) − 1 show that its letters are the original "
                        + "prefix read backwards. Its last letter compares floor(−δ) with "
                        + "floor(−α − δ) = −1. For δ = 0 it is true, and for δ > 0 it is false. "
                        + "The factor language of an irrational lower mechanical word is independent "
                        + "of the intercept, by lowerMechanicalFactor_mem_factorSet. Hence both "
                        + "extensions occur also in the word with intercept α. Removing the final "
                        + "letter from an occurrence shows that the reversed prefix itself occurs, "
                        + "so it is right-special.")),
                    Paragraph(Text(
                        "Now analyze the separator encoding. Cutting takes only the values 1 and 3. "
                        + "Thus rotor(σ, i) = 0 exactly when i = 0, and rotor(σ, i) = 2 exactly "
                        + "when i is odd. Every symbol other than 2 is followed by 2. If a "
                        + "nonempty rotor factor of length ℓ has two distinct continuations, neither "
                        + "occurrence can start at zero: equality of their first letters would force "
                        + "both starts to be zero and their continuations to agree. The factor "
                        + "must end in 2, since any other last letter forces the same next letter 2. "
                        + "For its positive occurrence starts i and j, both i + ℓ and j + ℓ are even.")),
                    Paragraph(Text(
                        "For a positive start i with i + ℓ even, the letter at offset t is 2 "
                        + "when t + ℓ is odd. Otherwise it encodes the mechanical bit at index "
                        + "(i − 1) / 2 + t / 2. Reading the nonseparator offsets 2q + ℓ % 2 "
                        + "therefore projects the rotor factor to a mechanical factor of length "
                        + "ℓ / 2 starting at (i − 1) / 2. The two rotor occurrences give the same "
                        + "mechanical factor, since the encoding false ↦ 1, true ↦ 3 is injective. "
                        + "Their next mechanical bits are distinct, since their next rotor "
                        + "symbols are distinct. The projected factor is consequently right-special.")),
                    Paragraph(Text(
                        "Apply exists_unique_lower_mechanical_right_special at slope and intercept α "
                        + "and length ℓ / 2. The projections of any two right-special rotor "
                        + "factors of length ℓ must coincide. The letter formula reconstructs "
                        + "the rotor factors from their common projection and the parity of t + ℓ, "
                        + "so the rotor factors coincide as well. This proves uniqueness.")),
                    Paragraph(Text(
                        "To identify that factor, let m = ℓ / 2, let p be the reversed length m "
                        + "mechanical prefix, and let u be the reversal of the rotor letters at "
                        + "positions 1 through ℓ. For either Boolean b, choose an occurrence of "
                        + "p followed by b in the mechanical word, starting at k. Set "
                        + "i = 2k + 2 − ℓ % 2. Then i > 0, i + ℓ is even, and (i − 1) / 2 = k. "
                        + "The same letter formula shows that the rotor word starting at i is u "
                        + "followed by the encoding of b: separator positions agree by parity, "
                        + "and the remaining positions agree with the reversed mechanical prefix. "
                        + "Taking b false and true supplies the distinct continuations 1 and 3. "
                        + "Thus u is right-special, including the case m = 0.")),
                    Paragraph(Text(
                        "Finally take ℓ = n − 1. The assumption n ≥ 2 gives ℓ > 0. The constructed "
                        + "word u has length ℓ and is right-special. Uniqueness forces every "
                        + "right-special w of that length to equal u; conversely, equality with u "
                        + "gives the right-special condition. These are the two directions of "
                        + "the claimed equivalence."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("krishnaswami-rameshan-2026-rotor-right-special-word"),
                    ResolutionKind.Proved)))));

    private static Formula CuttingFormula()
    {
        Formula index = Some("k", Naturals, And(LE(D(1), X("k")),
            Equal(X("m"), Add(
                Typed(Apply(Qualified("Nat", "floor"), Multiply(CastReal(X("k")), X("σ"))), Naturals),
                X("k")))));
        return All("σ", Reals, All("m", Naturals,
            Equal(Typed(Call("cutting", X("σ"), X("m")), Naturals),
                If(index, D(3), D(1)))));
    }

    private static Formula RotorFormula() => All("σ", Reals, All("m", Naturals,
        Equal(Typed(Call("rotor", X("σ"), X("m")), Naturals),
            If(Equal(X("m"), D(0)), D(0),
                If(Equal(Mod(X("m"), D(2)), D(1)), D(2),
                    Call("cutting", X("σ"), Divide(X("m"), D(2))))))));

    private static Formula FactorFormula() => SequenceBinders(Equivalence(
        Call("IsFactor", X("R"), X("w")),
        Some("i", Naturals, All("t", Naturals,
            All("h", LT(X("t"), Length(X("w"))),
                Equal(Apply(X("R"), Add(X("i"), X("t"))),
                    Apply(Qualified("GetElem", "getElem"), X("w"), X("t"), X("h"))))))));

    private static Formula RightSpecialFormula()
    {
        Formula extensions = And(
            Call("IsFactor", X("R"), Append(X("w"), Singleton(X("a")))),
            Call("IsFactor", X("R"), Append(X("w"), Singleton(X("b")))));
        return SequenceBinders(Equivalence(Call("IsRightSpecial", X("R"), X("w")),
            Some("a", Naturals, Some("b", Naturals,
                And(new Formula.Relation(X("a"), FormulaRelationOperator.NotEqual, X("b")), extensions)))));
    }

    private static Formula ClaimFormula()
    {
        Formula prefix = Apply(Qualified("List", "ofFn"),
            LambdaOf("t", Call("Fin", Subtract(X("n"), D(1))),
                Call("rotor", X("σ"),
                    Add(Typed(Apply(Qualified("Fin", "val"), X("t")), Naturals), D(1)))));
        Formula characterization = Equivalence(
            Call("IsRightSpecial", Call("rotor", X("σ")), X("w")),
            Equal(X("w"), Apply(Qualified("List", "reverse"), prefix)));
        return All("σ", Reals, Imp(Call("Irrational", X("σ")),
            Imp(LT(Typed(D(1), Reals), X("σ")), All("n", Naturals,
                Imp(LE(D(2), X("n")), All("w", ListNaturals,
                    Imp(Equal(Length(X("w")), Subtract(X("n"), D(1))), characterization)))))));
    }

    private static Formula SequenceBinders(Formula body) =>
        All("R", new Formula.TypeArrow(Naturals, Naturals), All("w", ListNaturals, body));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ListNaturals => Apply(Op("List"), Naturals);
    private static Formula X(string name) => name == "σ" ? SigmaLower : F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => Apply(Op(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula CastReal(Formula value) =>
        Typed(Apply(Qualified("Nat", "cast"), value), Reals);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(Parenthesized(left), FormulaRelationOperator.Equal, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(Parenthesized(left), FormulaRelationOperator.LessThanOrEqual, Parenthesized(right));
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(Parenthesized(left), FormulaRelationOperator.LessThan, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Divide(Formula left, Formula right) =>
        Apply(Qualified("Nat", "div"), left, right);
    private static Formula Mod(Formula left, Formula right) => Apply(Qualified("Nat", "mod"), left, right);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Call("ite", Parenthesized(condition), Parenthesized(yes), Parenthesized(no));
    private static Formula Length(Formula value) => Apply(Qualified("List", "length"), value);
    private static Formula Append(Formula left, Formula right) => Apply(Qualified("List", "append"), left, right);
    private static Formula Singleton(Formula value) => Seq(OpenBracket, value, CloseBracket);
}
