using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenChronology;

internal sealed class BinaryParikhStepTwoBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mateescu2001parikh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordered product of binary unipotent matrices records the two letter counts and the scattered true-before-false count. The same counts determine the represented step-two Chen signature and its doubled Magnus center.",
        H("Binary Parikh matrices and step-two Chen coordinates"),
        Blocks(
            Node("integer-matrices", "The integer matrix algebra", "IntegerMatrix3", DescribeRole.Definition,
                Disp(Equal(new Formula.Subscript(F.Id("M"), D(3)),
                    Call("Matrix", Call("Fin", D(3)), Call("Fin", D(3)), F.Id("Int")))),
                "M with subscript three denotes IntegerMatrix3, the algebra of three-by-three integer matrices with rows and columns indexed by zero, one and two. Write matrixUnit(a,b) for the matrix whose sole nonzero entry is one at (a,b)."),
            Node("letter-observation", "Nilpotent letter observations", "binaryLetterObservation", DescribeRole.Definition,
                LetterFormula(),
                "A true letter contributes the matrix unit at (0,1); a false letter contributes the unit at (1,2). Multiplication in that order produces the unit at (0,2), whereas the reverse product is zero. Each individual letter matrix has square zero."),
            Node("scattered-pairs", "The ordered scattered-pair counter", "scatteredTrueFalseCount", DescribeRole.Definition,
                PairDefinitionFormula(),
                "K(w) abbreviates scatteredTrueFalseCount(w). It counts pairs of positions with an earlier true letter and a later false letter, allowing any intervening letters. A leading true pairs with every false in the tail; a leading false contributes no new such pair."),
            Node("append-pair", "Appending a letter", "scattered_true_false_count_append_letter", DescribeRole.Theorem,
                AppendFormula(),
                "Appending true adds no true-before-false pair. Appending false adds one pair for every true already in the word. The formula includes the empty word."),
            Node("count-length", "The two counts exhaust length", "binary_letter_counts_length", DescribeRole.Theorem,
                LengthFormula(),
                "Every position of a binary word is either true or false. Thus the two natural counts sum to its length, including length zero."),
            Node("parikh-product", "The ordered unipotent product", "binaryParikhMatrix", DescribeRole.Definition,
                ProductFormula(),
                "P(w) abbreviates binaryParikhMatrix(w). The product is taken from left to right in word order, and one is the identity matrix. The empty product is the identity. With r and f the true and false counts, its diagonal entries are one, its lower entries are zero, and its upper entries (0,1), (1,2), (0,2) are r, f, K. Multiplying two such matrices adds the counts and adds the cross term r times the second word's false count to K.", literature: true),
            Node("parikh-entries", "The three Parikh entries", "binary_parikh_matrix_entries", DescribeRole.Theorem,
                EntriesFormula(false),
                "The displayed counts are cast from the naturals to the integers. The central matrix entry retains ordered scattered pairs, rather than adjacent transitions.", literature: true),
            Node("chen-entries", "The represented Chen entries", "binary_step_two_signature_entries", DescribeRole.Theorem,
                EntriesFormula(true),
                "S(w) denotes chronologicalSignature(binaryLetterObservation,w). Its degreeOne matrix has the true and false counts at (0,1) and (1,2), and zero elsewhere. Its doubledDegreeTwo matrix has 2K at (0,2) and zero elsewhere. Chen composition gives the same cross term as the unipotent product; the degree-two convention is factorial, so it has no division."),
            Node("magnus-center", "The doubled central Magnus coordinate", "binary_doubled_magnus_center", DescribeRole.Theorem,
                CenterFormula(),
                "C(w) denotes the (0,2) entry of doubledMagnusDegreeTwo(S(w)). Subtracting the square of degreeOne from doubledDegreeTwo gives 2K minus the product of the letter counts. This statement holds for every binary word, including empty and pure-letter words, whose center is zero."),
            Node("matrix-recovery", "Counts and center recover the matrix", "binary_parikh_eq_of_counts_and_magnus", DescribeRole.Theorem,
                RecoveryFormula(),
                "If two arbitrary words have the same true count, false count and doubled central Magnus entry, their pair counts agree by the integral center formula, and hence their complete Parikh matrices agree. This recovers the matrix; different ordered words can still have the same matrix.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula WordType() => Call("List", F.Id("Bool"));
    private static Formula Count(Formula w, string letter) => Call("count", w, F.Id(letter));
    private static Formula Integer(Formula n) => Call("integer", n);
    private static Formula Pairs(Formula w) => Call("K", w);
    private static Formula Signature(Formula w) => Call("S", w);
    private static Formula Center(Formula w) => Call("C", w);
    private static Formula Entry(Formula matrix, byte row, byte column) => new Formula.Apply(matrix, [D(row), D(column)]);

    private static Formula LetterFormula()
    {
        Formula b = F.Id("b");
        return Disp(All("b", F.Id("Bool"), Equal(Call("binaryLetterObservation", b),
            Call("if", b, Call("matrixUnit", D(0), D(1)), Call("matrixUnit", D(1), D(2))))));
    }

    private static Formula PairDefinitionFormula()
    {
        Formula w = F.Id("w");
        return Disp(And(Equal(Pairs(Seq(OpenBracket, CloseBracket)), D(0)), All("w", WordType(), And(
            Equal(Pairs(Call("cons", F.Id("true"), w)), Add(Count(w, "false"), Pairs(w))),
            Equal(Pairs(Call("cons", F.Id("false"), w)), Pairs(w))))));
    }

    private static Formula AppendFormula()
    {
        Formula w = F.Id("w"), b = F.Id("b");
        return Disp(All("w", WordType(), All("b", F.Id("Bool"), Equal(
            Pairs(Call("append", w, Seq(OpenBracket, b, CloseBracket))),
            Add(Pairs(w), Call("if", Equal(b, F.Id("true")), D(0), Count(w, "true")))))));
    }

    private static Formula LengthFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(Add(Count(w, "true"), Count(w, "false")), Call("length", w))));
    }

    private static Formula ProductFormula()
    {
        Formula w = F.Id("w"), k = F.Id("k");
        Formula product = Seq(Prod, Underscore, Grp(k, InMacro, Sp, Call("range", Call("length", w))),
            Seq(Open, Add(D(1), Call("binaryLetterObservation", Call("get", w, k))), Close));
        return Disp(All("w", WordType(), Equal(Call("P", w), product)));
    }

    private static Formula EntriesFormula(bool chen)
    {
        Formula w = F.Id("w"), first = chen ? Call("degreeOne", Signature(w)) : Call("P", w),
            second = chen ? Call("doubledDegreeTwo", Signature(w)) : Call("P", w);
        Formula pairs = Integer(Pairs(w));
        return Disp(All("w", WordType(), And(Equal(Entry(first, 0, 1), Integer(Count(w, "true"))), And(
            Equal(Entry(first, 1, 2), Integer(Count(w, "false"))),
            Equal(Entry(second, 0, 2), chen ? Mul(D(2), pairs) : pairs)))));
    }

    private static Formula CenterFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(
            Entry(Call("doubledMagnusDegreeTwo", Call("chronologicalSignature", Name("binaryLetterObservation"), w)), 0, 2),
            Sub(Mul(D(2), Integer(Pairs(w))), Mul(Integer(Count(w, "true")), Integer(Count(w, "false")))))));
    }

    private static Formula RecoveryFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        return Disp(All("a", WordType(), All("b", WordType(), Implies(Equal(Count(a, "true"), Count(b, "true")),
            Implies(Equal(Count(a, "false"), Count(b, "false")), Implies(Equal(Center(a), Center(b)),
                Equal(Call("P", a), Call("P", b))))))));
    }
}
