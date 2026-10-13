using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GenericLieLengthFiltrationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/GenericLieLengthFiltration.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/jiacapel2024genericlielength");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right-nested words, their length filtration and dimension estimates.",
        H("GenericLieLengthFiltration"),
        Blocks(
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-suset"),
                DeclarationHandle.Create(Prefix + "suSet"), H("suSet"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The real submodule consists of skew-Hermitian matrices with zero trace."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-sulie"),
                DeclarationHandle.Create(Prefix + "suLie"), H("suLie"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same carrier is a real Lie subalgebra with the matrix commutator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-layer"),
                DeclarationHandle.Create(Prefix + "layer"), H("layer"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 3 (arXiv:2301.08241v3, p. 17) defines the layers by “U₁ = span{U}; Uₙ = span[U,Uₙ₋₁], n ≥ 2.” The zero layer is bottom, and the positive layers have exactly the source recurrence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-lielength"),
                DeclarationHandle.Create(Prefix + "lieLength"), H("lieLength"),
                StatementSource.FromAuthor(Formula3()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 3 (arXiv:2301.08241v3, p. 17): “The Lie-length of a Lie-generating system U of a finite-dimensional Lie-algebra A is the minimal length of the (right-nested) brackets such that the brackets span the whole Lie-algebra, namely Lieℓ(U)=min{ℓ | A=span{Uₙ, n≤ℓ}}, where Uₙ is defined as: U₁=span{U}; Uₙ=span[U,Uₙ₋₁], n≥2.” Natural sInf returns zero for an empty set; the asserted bounds apply to samples for which the layers span suSet."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-sucoordinatemap"),
                DeclarationHandle.Create(Prefix + "suCoordinateMap"), H("suCoordinateMap"),
                StatementSource.FromAuthor(Formula4()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Module.finBasis supplies real coordinates for the traceless skew-Hermitian submodule. The map sends each generator coordinate vector through the inverse basis equivalence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-supairmeasure"),
                DeclarationHandle.Create(Prefix + "suPairMeasure"), H("suPairMeasure"),
                StatementSource.FromAuthor(Formula5()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The measure is the pushforward of real coordinate Lebesgue measure. Matrices use their entries as functions Fin n → Fin n → ℂ. Almost everywhere therefore means outside a Lebesgue null set of generator coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightword"),
                DeclarationHandle.Create(Prefix + "RightWord"), H("RightWord"),
                StatementSource.FromAuthor(Formula6()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("RightWord is the inductive type with precisely the single and cons constructors. It represents nonempty right-nested brackets."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightword-length"),
                DeclarationHandle.Create(Prefix + "rightWordLength"), H("rightWordLength"),
                StatementSource.FromAuthor(Formula7()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Length counts generator letters."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightword-eval"),
                DeclarationHandle.Create(Prefix + "rightWordEval"), H("rightWordEval"),
                StatementSource.FromAuthor(Formula8()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluation uses the right-nested Lie bracket."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightspan"),
                DeclarationHandle.Create(Prefix + "rightSpan"), H("rightSpan"),
                StatementSource.FromAuthor(Formula9()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The submodule is spanned by evaluations of words of length at most L."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-word-mem"),
                DeclarationHandle.Create(Prefix + "word_mem"), H("word_mem"),
                StatementSource.FromAuthor(Formula10()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each sufficiently short word belongs to the defining span."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightspan-mono"),
                DeclarationHandle.Create(Prefix + "rightSpan_mono"), H("rightSpan_mono"),
                StatementSource.FromAuthor(Formula11()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Increasing the length cutoff enlarges the span."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-word-bracket-mem"),
                DeclarationHandle.Create(Prefix + "word_bracket_mem"), H("word_bracket_mem"),
                StatementSource.FromAuthor(Formula12()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Jacobi induction moves brackets into the right-nested filtration and adds the two lengths."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightspan-bracket-mem"),
                DeclarationHandle.Create(Prefix + "rightSpan_bracket_mem"), H("rightSpan_bracket_mem"),
                StatementSource.FromAuthor(Formula13()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bilinearity extends the word estimate to both spans."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-polynomial-ad-mem"),
                DeclarationHandle.Create(Prefix + "polynomial_ad_mem"), H("polynomial_ad_mem"),
                StatementSource.FromAuthor(Formula14()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A polynomial in the generator adjoint increases the length by at most its natural degree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightspan-real-le-su"),
                DeclarationHandle.Create(Prefix + "rightSpan_real_le_su"), H("rightSpan_real_le_su"),
                StatementSource.FromAuthor(Formula15()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Skew-Hermitian trace-zero generators stay in the same submodule under real linear combinations and brackets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightspan-complex-to-real"),
                DeclarationHandle.Create(Prefix + "rightSpan_complex_to_real"), H("rightSpan_complex_to_real"),
                StatementSource.FromAuthor(Formula16()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The skew-adjoint projection replaces every complex coefficient by its real part on a skew-Hermitian word. Complex spanning therefore transfers to the real form."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-rightspan-reindex-le"),
                DeclarationHandle.Create(Prefix + "rightSpan_reindex_le"), H("rightSpan_reindex_le"),
                StatementSource.FromAuthor(Formula17()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Relabeling generator indices preserves evaluations and word lengths."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-lielength-le-of-span"),
                DeclarationHandle.Create(Prefix + "lieLength_le_of_span"), H("lieLength_le_of_span"),
                StatementSource.FromAuthor(Formula18()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cumulative source layers equal the bounded-word span, so saturation bounds the source Lie-length."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-words"),
                DeclarationHandle.Create(Prefix + "words"), H("words"),
                StatementSource.FromAuthor(Formula19()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite enumeration consists of single letters and words formed by prepending a letter."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-wordbudget"),
                DeclarationHandle.Create(Prefix + "wordBudget"), H("wordBudget"),
                StatementSource.FromAuthor(Formula20()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The recurrence equals the sum of g to powers 1 through L."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-card-words-le"),
                DeclarationHandle.Create(Prefix + "card_words_le"), H("card_words_le"),
                StatementSource.FromAuthor(Formula21()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Union and image cardinalities bound the number of enumerated words."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-lower-lielength-of-saturation"),
                DeclarationHandle.Create(Prefix + "lower_lieLength_of_saturation"), H("lower_lieLength_of_saturation"),
                StatementSource.FromAuthor(Formula22()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real dimension n² − 1 cannot exceed the number of words. Bounding the word budget by (g + 1) to the cutoff yields this logarithmic lower bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthfiltration-upper-log"),
                DeclarationHandle.Create(Prefix + "upper_log"), H("upper_log"),
                StatementSource.FromAuthor(Formula23()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nat.log 2 is the integer base-two logarithm. The cast encloses the natural expression on the left; the right-hand logarithm is real."))), DescribeRole.Theorem)),
        []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Apply(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("X"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("X"), Sp, InMacro, Sp, Named("suSet"), Sp, F.Id("n"), Sp, Iff, Sp, Parenthesized(Seq(Apply(Qualified("Matrix", "conjTranspose"), F.Id("X")), Sp, Eq, Sp, Minus, Sp, F.Id("X"), Sp, Land, Sp, Named("Matrix"), Sp, Dot, Sp, Named("trace"), Sp, F.Id("X"), Sp, Eq, Sp, D(0)))));

    private static Formula Formula1() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("X"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("X"), Sp, InMacro, Sp, Named("suLie"), Sp, F.Id("n"), Sp, Iff, Sp, F.Id("X"), Sp, InMacro, Sp, Named("suSet"), Sp, F.Id("n")));

    private static Formula Formula2() => Disp(
        new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Finset"), Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, Named("layer"), Sp, F.Id("S"), Sp, D(0), Sp, Eq, Sp, Qualified("Bot", "bot")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Finset"), Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, Named("layer"), Sp, F.Id("S"), Sp, D(1), Sp, Eq, Sp, Named("Submodule"), Sp, Dot, Sp, Named("span"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Set"), Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))))))), Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Finset"), Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, Named("layer"), Sp, F.Id("S"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(2))), Sp, Eq, Sp, Named("Submodule"), Sp, Dot, Sp, Named("span"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, OpenBrace, Sp, F.Id("Z"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Mid, Sp, Exists, Sp, Parenthesized(Seq(F.Id("X"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("X"), Sp, InMacro, Sp, F.Id("S"), Sp, Land, Sp, Exists, Sp, Parenthesized(Seq(F.Id("Y"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("Y"), Sp, InMacro, Sp, Named("layer"), Sp, F.Id("S"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))), Sp, Land, Sp, F.Id("Z"), Sp, Eq, Sp, OpenBracket, Sp, F.Id("X"), Sp, Comma, Sp, F.Id("Y"), Sp, CloseBracket, Sp, CloseBrace)]));

    private static Formula Formula3() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Finset"), Sp, Parenthesized(Seq(Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, Named("lieLength"), Sp, F.Id("n"), Sp, F.Id("S"), Sp, Eq, Sp, Named("sInf"), Sp, OpenBrace, Sp, F.Id("l"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mid, Sp, D(1), Sp, Leq, Sp, F.Id("l"), Sp, Land, Sp, Parenthesized(Seq(Seq(Named("iSup"), Underscore, Grp(Seq(F.Id("k"), Colon, Seq(Mathbb, Grp(F.Id("N"))), InMacro, Seq(Named("Finset"), Sp, Dot, Sp, Named("Icc"), Sp, D(1), Sp, F.Id("l"))))), Sp, Named("layer"), Sp, F.Id("S"), Sp, F.Id("k"))), Sp, Eq, Sp, Named("suSet"), Sp, F.Id("n"), Sp, CloseBrace));

    private static Formula Formula4() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, Named("Fin"), Sp, Parenthesized(Seq(Named("Module"), Sp, Dot, Sp, Named("finrank"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Parenthesized(Seq(Named("suSet"), Sp, F.Id("n"))))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"))), Sp, Comma, Sp, Named("suCoordinateMap"), Sp, F.Id("g"), Sp, F.Id("n"), Sp, F.Id("x"), Sp, F.Id("j"), Sp, Eq, Sp, Named("Subtype"), Sp, Dot, Sp, Named("val"), Sp, Parenthesized(Seq(Parenthesized(Seq(Named("Module"), Sp, Dot, Sp, Named("finBasis"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Parenthesized(Seq(Named("suSet"), Sp, F.Id("n"))))), Sp, Dot, Sp, Named("equivFun"), Sp, Dot, Sp, Named("symm"), Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("j")))))));

    private static Formula Formula5() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("suPairMeasure"), Sp, F.Id("g"), Sp, F.Id("n"), Sp, Eq, Sp, Named("MeasureTheory"), Sp, Dot, Sp, Named("Measure"), Sp, Dot, Sp, Named("map"), Sp, Parenthesized(Seq(Named("suCoordinateMap"), Sp, F.Id("g"), Sp, F.Id("n"))), Sp, Named("volume")));

    private static Formula Formula6() => Disp(
        new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, Comma, Sp, Named("RightWord"), Sp, Dot, Sp, Named("single"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, Named("RightWord"), Sp, F.Id("I")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, Comma, Sp, Named("RightWord"), Sp, Dot, Sp, Named("cons"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, Named("RightWord"), Sp, F.Id("I"), Sp, To, Sp, Named("RightWord"), Sp, F.Id("I"))]));

    private static Formula Formula7() => Disp(
        new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Comma, Sp, Named("rightWordLength"), Sp, Parenthesized(Seq(Named("RightWord"), Sp, Dot, Sp, Named("single"), Sp, F.Id("i"))), Sp, Eq, Sp, D(1)), Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Named("RightWord"), Sp, F.Id("I"))), Sp, Comma, Sp, Named("rightWordLength"), Sp, Parenthesized(Seq(Named("RightWord"), Sp, Dot, Sp, Named("cons"), Sp, F.Id("i"), Sp, F.Id("w"))), Sp, Eq, Sp, Named("rightWordLength"), Sp, F.Id("w"), Sp, Plus, Sp, D(1))]));

    private static Formula Formula8() => Disp(
        new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Comma, Sp, Named("rightWordEval"), Sp, F.Id("S"), Sp, Parenthesized(Seq(Named("RightWord"), Sp, Dot, Sp, Named("single"), Sp, F.Id("i"))), Sp, Eq, Sp, F.Id("S"), Sp, F.Id("i")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Named("RightWord"), Sp, F.Id("I"))), Sp, Comma, Sp, Named("rightWordEval"), Sp, F.Id("S"), Sp, Parenthesized(Seq(Named("RightWord"), Sp, Dot, Sp, Named("cons"), Sp, F.Id("i"), Sp, F.Id("w"))), Sp, Eq, Sp, OpenBracket, Sp, F.Id("S"), Sp, F.Id("i"), Sp, Comma, Sp, Named("rightWordEval"), Sp, F.Id("S"), Sp, F.Id("w"), Sp, CloseBracket)]));

    private static Formula Formula9() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("L"), Sp, Eq, Sp, Named("Submodule"), Sp, Dot, Sp, Named("span"), Sp, F.Id("K"), Sp, OpenBrace, Sp, F.Id("x"), Sp, Colon, Sp, F.Id("M"), Sp, Mid, Sp, Exists, Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Named("RightWord"), Sp, F.Id("I"))), Sp, Comma, Sp, F.Id("w"), Sp, Dot, Sp, Named("rightWordLength"), Sp, Leq, Sp, F.Id("L"), Sp, Land, Sp, Named("rightWordEval"), Sp, F.Id("S"), Sp, F.Id("w"), Sp, Eq, Sp, F.Id("x"), Sp, CloseBrace));

    private static Formula Formula10() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, Named("RightWord"), Sp, F.Id("I"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("w"), Sp, Dot, Sp, Named("rightWordLength"), Sp, Leq, Sp, F.Id("L"), Sp, To, Sp, Named("rightWordEval"), Sp, F.Id("S"), Sp, F.Id("w"), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("L")));

    private static Formula Formula11() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("a"), Sp, Leq, Sp, F.Id("b"), Sp, To, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("a"), Sp, Leq, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("b")));

    private static Formula Formula12() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("u"), Sp, F.Id("v"), Sp, Colon, Sp, Named("RightWord"), Sp, F.Id("I"))), Sp, Comma, Sp, OpenBracket, Sp, Named("rightWordEval"), Sp, F.Id("S"), Sp, F.Id("u"), Sp, Comma, Sp, Named("rightWordEval"), Sp, F.Id("S"), Sp, F.Id("v"), Sp, CloseBracket, Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, Parenthesized(Seq(F.Id("u"), Sp, Dot, Sp, Named("rightWordLength"), Sp, Plus, Sp, F.Id("v"), Sp, Dot, Sp, Named("rightWordLength")))));

    private static Formula Formula13() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, F.Id("M"))), Sp, Comma, Sp, F.Id("x"), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("r"), Sp, To, Sp, F.Id("y"), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("t"), Sp, To, Sp, OpenBracket, Sp, F.Id("x"), Sp, Comma, Sp, F.Id("y"), Sp, CloseBracket, Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, F.Id("t")))));

    private static Formula Formula14() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Named("Polynomial"), Sp, F.Id("K"))), Sp, Comma, Sp, F.Id("x"), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("L"), Sp, To, Sp, Named("Polynomial"), Sp, Dot, Sp, Named("aeval"), Sp, Parenthesized(Seq(Named("LieAlgebra"), Sp, Dot, Sp, Named("ad"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("i"))))), Sp, F.Id("p"), Sp, F.Id("x"), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Plus, Sp, F.Id("p"), Sp, Dot, Sp, Named("natDegree")))));

    private static Formula Formula15() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Comma, Sp, F.Id("S"), Sp, F.Id("i"), Sp, InMacro, Sp, Named("suSet"), Sp, F.Id("n"))), Sp, To, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, F.Id("S"), Sp, F.Id("L"), Sp, Leq, Sp, Named("suSet"), Sp, F.Id("n")));

    private static Formula Formula16() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("X"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Comma, Sp, F.Id("S"), Sp, F.Id("i"), Sp, InMacro, Sp, Named("suSet"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("X"), Sp, InMacro, Sp, Named("suSet"), Sp, F.Id("n"), Sp, To, Sp, F.Id("X"), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, F.Id("S"), Sp, F.Id("L"), Sp, To, Sp, F.Id("X"), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, F.Id("S"), Sp, F.Id("L")));

    private static Formula Formula17() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("J"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("J"))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("T"), Sp, Colon, Sp, F.Id("J"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Comma, Sp, F.Id("T"), Sp, Parenthesized(Seq(F.Id("f"), Sp, F.Id("i"))), Sp, Eq, Sp, F.Id("S"), Sp, F.Id("i"))), Sp, To, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("L"), Sp, Leq, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("T"), Sp, F.Id("L")));

    private static Formula Formula18() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("n"), Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, D(1), Sp, Leq, Sp, F.Id("L"), Sp, To, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, F.Id("S"), Sp, F.Id("L"), Sp, Eq, Sp, Named("suSet"), Sp, F.Id("n"), Sp, To, Sp, Named("lieLength"), Sp, F.Id("n"), Sp, Parenthesized(Seq(Named("Finset"), Sp, Dot, Sp, Named("univ"), Sp, Dot, Sp, Named("image"), Sp, F.Id("S"))), Sp, Leq, Sp, F.Id("L")));

    private static Formula Formula19() => Disp(
        new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("words"), Sp, F.Id("g"), Sp, D(0), Sp, Eq, Sp, Emptyset), Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("words"), Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, Named("Finset"), Sp, Dot, Sp, Named("univ"), Sp, Dot, Sp, Named("image"), Sp, Named("RightWord"), Sp, Dot, Sp, Named("single"), Sp, Cup, Sp, Named("Finset"), Sp, Dot, Sp, Named("univ"), Sp, Dot, Sp, Named("biUnion"), Sp, Parenthesized(Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"))), Sp, Mapsto, Sp, Parenthesized(Seq(Named("words"), Sp, F.Id("g"), Sp, F.Id("L"))), Sp, Dot, Sp, Named("image"), Sp, Parenthesized(Seq(Named("RightWord"), Sp, Dot, Sp, Named("cons"), Sp, F.Id("i"))))))]));

    private static Formula Formula20() => Disp(
        new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("wordBudget"), Sp, F.Id("g"), Sp, D(0), Sp, Eq, Sp, D(0)), Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("wordBudget"), Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, F.Id("g"), Sp, Plus, Sp, F.Id("g"), Sp, Star, Sp, Named("wordBudget"), Sp, F.Id("g"), Sp, F.Id("L"))]));

    private static Formula Formula21() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(Named("words"), Sp, F.Id("g"), Sp, F.Id("L"))), Sp, Dot, Sp, Named("card"), Sp, Leq, Sp, Named("wordBudget"), Sp, F.Id("g"), Sp, F.Id("L")));

    private static Formula Formula22() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("g"), Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("g"), Sp, To, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, D(2), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, D(2), Sp, Leq, Sp, F.Id("g"), Sp, To, Sp, D(1), Sp, Leq, Sp, F.Id("L"), Sp, To, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, F.Id("S"), Sp, F.Id("L"), Sp, Eq, Sp, Named("suSet"), Sp, F.Id("n"), Sp, To, Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, Named("Real"), Sp, Dot, Sp, Named("log"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(1))))), Sp, Star, Sp, Named("Real"), Sp, Dot, Sp, Named("log"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Leq, Sp, Parenthesized(Seq(Named("lieLength"), Sp, F.Id("n"), Sp, Parenthesized(Seq(Named("Finset"), Sp, Dot, Sp, Named("univ"), Sp, Dot, Sp, Named("image"), Sp, F.Id("S"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))))));

    private static Formula Formula23() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1, 6), Sp, Star, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Named("Nat"), Sp, Dot, Sp, Named("log"), Sp, D(2), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Leq, Sp, Parenthesized(Seq(D(3, 2), Sp, Slash, Sp, Named("Real"), Sp, Dot, Sp, Named("log"), Sp, D(2))), Sp, Star, Sp, Named("Real"), Sp, Dot, Sp, Named("log"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(2)))));
}
