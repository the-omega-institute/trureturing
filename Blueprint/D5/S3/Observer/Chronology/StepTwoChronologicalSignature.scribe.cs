using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoChronologicalSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepTwoChronologicalSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Step-two signatures obey Chen concatenation and the degree-two BCH "
            + "law.",
        H("Step-Two Chronological Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("step-two-signature"),
                DeclarationHandle.Create(Prefix + "StepTwoSignature"),
                H("Step-two signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A step-two signature stores degree one together with twice degree two, "
                        + "so the construction requires no division by two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("event-signature"),
                DeclarationHandle.Create(Prefix + "eventSignature"),
                H("Single-event signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One event contributes its algebra value at degree one and its square "
                        + "to doubled degree two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chronological-signature"),
                DeclarationHandle.Create(Prefix + "chronologicalSignature"),
                H("Chronological word signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signature of a list composes single-event signatures from left to "
                        + "right in operational chronology."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chen-append"),
                DeclarationHandle.Create(Prefix + "chronological_signature_append"),
                H("Step-two Chen identity"),
                StatementSource.FromAuthor(AppendFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signature of an earlier word followed by a later word is their "
                        + "chronological signature product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degree-one"),
                DeclarationHandle.Create(Prefix + "chronological_signature_degree_one"),
                H("Degree one forgets chronology"),
                StatementSource.FromAuthor(DegreeOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Degree one is the ordinary sum of all observed event values and is "
                        + "therefore insensitive to their order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("doubled-magnus"),
                DeclarationHandle.Create(Prefix + "doubledMagnusDegreeTwo"),
                H("Doubled degree-two Magnus coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtracting the square of degree one from doubled degree two extracts "
                        + "the doubled logarithmic coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bch-mul"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_degree_two_mul"),
                H("Degree-two BCH law"),
                StatementSource.FromAuthor(BchMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithmic coordinate of a product is the sum of the two "
                        + "coordinates plus the commutator of their degree-one parts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bch-append"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_degree_two_append"),
                H("Chronological BCH append law"),
                StatementSource.FromAuthor(BchAppendFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Combining Chen concatenation with the logarithmic coordinate gives the "
                            + "step-two BCH formula for two event words.")),
                    Paragraph(Text(
                        "An integer lattice application uses finite lists of "
                            + "LatticeWalkNearMaximalArea.Step: E, W, N and S mean right, left, "
                            + "up and down. All coordinates are integers, the walk starts at the "
                            + "origin, and the words have no region or path restrictions. With "
                            + "matrix indices 0, 1 and 2, let e_ij be the matrix unit and let "
                            + "T_ij(t) = I + t e_ij. These are the integer special-linear "
                            + "transvections supplied by Matrix.SpecialLinearGroup.transvection. "
                            + "Assign E and W to T_01(1) and T_01(-1), and N and S to T_12(1) "
                            + "and T_12(-1). The matrix signature sigma(w) is the ordered product "
                            + "of these letters, with earlier steps on the left; the empty "
                            + "word has signature I.")),
                    Paragraph(Text(
                        "Write H(x,y,z) for the upper triangular matrix with rows "
                            + "(1,x,z), (0,1,y), (0,0,1). Its transvection factorization is "
                            + "T_01(x) T_12(y) T_02(z-xy). Every word signature has this form, "
                            + "and x(w), y(w), z(w) are its entries 01, 12, 02. Thus x and y "
                            + "are the signed horizontal and vertical displacements. Matrix "
                            + "multiplication gives H(x,y,z) H(a,b,c) = "
                            + "H(x+a,y+b,z+c+xb), and concatenation gives "
                            + "sigma(uv) = sigma(u) sigma(v).")),
                    Paragraph(Text(
                        "If step i has displacement (dx_i,dy_i), then "
                            + "z(w) = sum over i<j of dx_i dy_j: each vertical step contributes "
                            + "its vertical increment times the preceding horizontal coordinate. "
                            + "This is the discrete integral of x dy. It differs from "
                            + "LatticeWalkNearMaximalArea.area, whose definition integrates "
                            + "y dx by charging horizontal steps at their current height. "
                            + "The two conventions must be kept distinct.")),
                    Paragraph(Text(
                        "To apply the chronological formulas, take the event type to be "
                            + "Step, the ring to be the 3-by-3 integer matrix ring, and "
                            + "observe(s) to be its assigned letter matrix minus I. Each event "
                            + "observation has square zero. Their sum has entries x and y at "
                            + "01 and 12, while their orderedPairMoment has entry z at 02. "
                            + "The stored doubled degree-two coordinate therefore has entry "
                            + "2z, and the square of degree one has entry xy. Consequently "
                            + "the 02 entry of doubledMagnusDegreeTwo is A(w) = 2z(w)-x(w)y(w). "
                            + "SignatureOrderedMoment.doubledMagnusDegreeTwo_eq_orderedPairMoment_sub_reverse "
                            + "also identifies A with the 02 entry of the ordered-pair moment "
                            + "minus the moment of the reversed observation list, namely the "
                            + "sum over i<j of dx_i dy_j-dy_i dx_j.")),
                    Paragraph(Text(
                        "The chronological BCH append law now reads "
                            + "A(uv) = A(u)+A(v)+x(u)y(v)-y(u)x(v). The last two terms are "
                            + "the 02 entry of the commutator of the degree-one matrices. "
                            + "Thus EN and NE have the same endpoint (1,1), but z(EN)=1 "
                            + "and z(NE)=0; their ordered matrix products differ. The closed "
                            + "word ENWS has signature H(0,0,1), whereas NESW has signature "
                            + "H(0,0,-1). A signed example is WN, with signature H(-1,1,-1).")),
                    Paragraph(Text(
                        "The inverse word reverses the list and replaces every step by "
                            + "its opposite, swapping E with W and N with S. The "
                            + "transvection inverse law sends each letter to its matrix "
                            + "inverse, so this actual word has signature sigma(w)^(-1). "
                            + "Since H(x,y,z)^(-1) = H(-x,-y,xy-z), its A coordinate is "
                            + "-A(w). Under observe this operation is reverse-and-negate, "
                            + "as in ChronologicalSignatureHopf.chronological_signature_reverse_neg. "
                            + "The number of E/W letters and the number of N/S letters "
                            + "each equal those of the original word.")),
                    Paragraph(Text(
                        "Every integer triple (x,y,z) is attained by an actual finite "
                            + "word. Indeed, the subgroup generated by T_01(1) and T_12(1) "
                            + "contains their commutator T_02(1), represented by ENWS. "
                            + "The transvection addition law identifies T_ij(t) with the "
                            + "integer power T_ij(1)^t. Hence the factorization of H(x,y,z) "
                            + "lies in this generated subgroup for all integers x,y,z. "
                            + "FreeGroup.range_lift_eq_closure and FreeGroup.lift_mk express "
                            + "this membership as a finite signed word in the two generators; "
                            + "decoding its signed letters as E, W, N and S yields the desired "
                            + "Step list and its complete matrix signature. In particular, "
                            + "at any fixed endpoint every integer z occurs. Appending ENWS "
                            + "or its inverse keeps that endpoint and changes z by +1 or "
                            + "-1, respectively.")),
                    Paragraph(Text(
                        "For every fixed integer endpoint, every natural modulus n and "
                            + "every residue r in ZMod n, choose an integer representative "
                            + "of r and realize that central coordinate by such a word. "
                            + "This includes every odd prime modulus. These are existence "
                            + "statements for unrestricted finite words. Prescribed length, "
                            + "simplicity, confinement to a region, unused-edge requirements, "
                            + "T adjacency and available empty squares impose further "
                            + "conditions. A central residue alone does not certify their "
                            + "feasibility, and these statements do not extend the "
                            + "near-maximal-area walk-counting result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-event-commutator"),
                DeclarationHandle.Create(
                    Prefix + "doubled_magnus_two_events_eq_commutator"),
                H("Two-event Magnus coordinate is the commutator"),
                StatementSource.FromAuthor(TwoEventsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a chronology containing exactly two events, the doubled "
                        + "degree-two logarithmic coordinate is their ring commutator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-event-swap"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_two_events_swap"),
                H("Two-event orientation reversal"),
                StatementSource.FromAuthor(SwapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing two events negates the degree-two chronological defect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("commuting-zero"),
                DeclarationHandle.Create(
                    Prefix + "doubled_magnus_two_events_eq_zero_of_commute"),
                H("Commuting events have zero defect"),
                StatementSource.FromAuthor(CommuteZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A commuting event pair has no degree-two chronological memory."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Sig(Formula word) =>
        Call("chronologicalSignature", F.Id("f"), word);

    private static Formula Mag(Formula signature) =>
        Call("doubledMagnusDegreeTwo", signature);

    private static Formula PairWord(Formula first, Formula second) =>
        Seq(OpenBracket, first, Comma, Sp, second, CloseBracket);

    private static Formula Joined() =>
        Call("append", F.Id("P"), F.Id("S"));

    private static Formula AppendFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("S"),
        Comma, Sp,
        Sig(Joined()), Sp, Eq, Sp,
        Sig(F.Id("P")), Sp, Cdot, Sp, Sig(F.Id("S")), Dot));

    private static Formula DegreeOneFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("L"), Comma, Sp,
        Call("degreeOne", Sig(F.Id("L"))), Sp, Eq, Sp,
        Call("sum", Call("map", F.Id("f"), F.Id("L"))), Dot));

    private static Formula BchMulFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
        Mag(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("b"))), Sp, Eq, Sp,
        Mag(F.Id("a")), Sp, Plus, Sp, Mag(F.Id("b")), Sp, Plus, Sp,
        Call("commutator",
            Call("degreeOne", F.Id("a")), Call("degreeOne", F.Id("b"))),
        Dot));

    private static Formula BchAppendFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("S"),
        Colon,
        RowBreak, Grp(),
        Mag(Sig(Joined())), Sp, Eq, Sp,
        Mag(Sig(F.Id("P"))), Sp, Plus, Sp, Mag(Sig(F.Id("S"))), Sp, Plus, Sp,
        Call("commutator",
            Call("degreeOne", Sig(F.Id("P"))),
            Call("degreeOne", Sig(F.Id("S")))), Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula TwoEventsFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("p"), Comma, Sp, F.Id("q"),
        Comma, Sp,
        Mag(Sig(PairWord(F.Id("p"), F.Id("q")))), Sp, Eq, Sp,
        Call("commutator",
            Call("f", F.Id("p")), Call("f", F.Id("q"))), Dot));

    private static Formula SwapFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("p"), Comma, Sp, F.Id("q"),
        Comma, Sp,
        Mag(Sig(PairWord(F.Id("q"), F.Id("p")))), Sp, Eq, Sp,
        Minus, Mag(Sig(PairWord(F.Id("p"), F.Id("q")))), Dot));

    private static Formula CommuteZeroFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("p"), Comma, Sp, F.Id("q"),
        Comma, Sp,
        Call("f", F.Id("p")), Sp, Cdot, Sp, Call("f", F.Id("q")),
        Sp, Eq, Sp,
        Call("f", F.Id("q")), Sp, Cdot, Sp, Call("f", F.Id("p")),
        Sp, Rightarrow, Sp,
        Mag(Sig(PairWord(F.Id("p"), F.Id("q")))), Sp, Eq, Sp, D(0), Dot));
}
