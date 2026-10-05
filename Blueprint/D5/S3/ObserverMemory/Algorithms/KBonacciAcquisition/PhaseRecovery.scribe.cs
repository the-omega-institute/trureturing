using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class PhaseRecoveryDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Safe literal KBonacci phase probes for block and single-bit alphabets.",
        H("PhaseRecovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kbonacci-isolated-probe-orbit-exact"),
                DeclarationHandle.Create(Owner + "isolated_probe_orbit_exact"),
                H("Literal isolated probes supply safe endpoint samples"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("r"), Colon,
                    Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("v"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("phi"),
                    Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
                    Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close), Sp, Land, Sp,
                    Seq(Open, Seq(D(1), Sp, Leq, Sp, F.Id("j")), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("j"), Sp, Lt, Sp, F.Id("m")),
                    Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s"), Sp, Lt, Sp, F.Id("k")), Close)), Close), Sp, Implies, Sp, Seq(Open,
                    Seq(Seq(Open, Call("DBonacciAdmissible", F.Id("k"), F.Id("m"), Call("isolatedProbe", F.Id("m"), F.Id("j"))),
                    Close), Sp, Land, Sp, Seq(Open, Seq(Exists, Sp, F.Id("s0"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                    Sp, Seq(Open, Seq(Seq(Open, Seq(F.Id("s0"), Sp, Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(Call("iterate",
                    Call("runBits", F.Id("k"), Call("isolatedProbe", F.Id("m"), F.Id("j"))), F.Id("r"), Call("some", F.Id("v"),
                    F.Id("phi"), F.Id("s"))), Sp, Eq, Sp, Call("some", Seq(F.Id("v"), Plus, Seq(Sum, Underscore, Grp(Seq(F.Id("i"),
                    Sp, Lt, Sp, F.Id("r"))), Sp, Call("coefficient", F.Id("k"), Seq(F.Id("phi"), Plus, Seq(Seq(F.Id("i"), Sp,
                    Cdot, Sp, F.Id("m")), Plus, F.Id("j")))))), Seq(F.Id("phi"), Plus, Seq(F.Id("r"), Sp, Cdot, Sp, F.Id("m"))),
                    F.Id("s0"))), Close)), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k at least two, natural m, j and r with 1<=j<m, "
                        + "value v, ambient phase phi and initial tail s below k, "
                        + "isolatedProbe(m,j) has its single true bit at j. It is "
                        + "locally legal. After r actual executions there is a "
                        + "tail s2 below k and the current record is "
                        + "(v+sum over i<r of coefficient(k,phi+im+j),phi+rm,s2). "
                        + "The orbit therefore never rejects, and adjacent complete "
                        + "endpoint values give the literal samples coefficient(k,phi+im+j). "
                        + "This supplies the execution and safety part of the "
                        + "multi-bit phase protocol. It does not by itself prove "
                        + "phase recovery from p-1 samples, the single-bit odd/even "
                        + "protocols, or the full acquisition criterion and bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-odd-single-bit-phase-recovery"),
                DeclarationHandle.Create(Owner + "odd_single_bit_phase_recovery"),
                H("The odd-period single-bit protocol recovers the initial phase"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("v1"), Colon, Sp, Call("ZMod",
                    D(2)), Comma, Sp, F.Id("v2"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("phi1"), Colon, Sp, Call("ZMod",
                    Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("phi2"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))),
                    Comma, Sp, F.Id("s1"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("s2"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close),
                    Sp, Land, Sp, Seq(Open, Call("Odd", Seq(F.Id("k"), Plus, D(1))), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s1"),
                    Sp, Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s2"), Sp, Lt, Sp, F.Id("k")), Close)), Close),
                    Sp, Implies, Sp, Seq(Open, Seq(Seq(Open, Seq(Forall, Sp, F.Id("r"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
                    Comma, Sp, Seq(Open, Seq(Exists, Sp, F.Id("s0"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(F.Id("s0"), Sp, Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(Call("alternatingBitOrbit",
                    F.Id("k"), F.Id("r"), Call("some", F.Id("v1"), F.Id("phi1"), F.Id("s1"))), Sp, Eq, Sp, Call("some", Seq(F.Id("v1"),
                    Plus, Seq(Sum, Underscore, Grp(Seq(F.Id("i"), Sp, Lt, Sp, F.Id("r"))), Sp, Call("coefficient", F.Id("k"),
                    Seq(F.Id("phi1"), Plus, Seq(Seq(F.Id("i"), Sp, Cdot, Sp, D(2)), Plus, D(1)))))), Seq(F.Id("phi1"), Plus, Seq(F.Id("r"),
                    Sp, Cdot, Sp, D(2))), F.Id("s0"))), Close)), Close)), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(Forall, Sp, F.Id("r"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(F.Id("r"),
                    Sp, Leq, Sp, Seq(F.Id("k"), Plus, D(1))), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("endpointReading", Call("alternatingBitOrbit",
                    F.Id("k"), F.Id("r"), Call("some", F.Id("v1"), F.Id("phi1"), F.Id("s1")))), Sp, Eq, Sp, Call("endpointReading",
                    Call("alternatingBitOrbit", F.Id("k"), F.Id("r"), Call("some", F.Id("v2"), F.Id("phi2"), F.Id("s2"))))), Close)),
                    Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(F.Id("phi1"), Sp, Eq, Sp, F.Id("phi2")), Close)), Close)),
                    Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k at least two with odd T=k+1, every two values in "
                        + "ZMod 2, ambient phases phi1 and phi2, and initial tails "
                        + "s1 and s2 below k, alternatingBitOrbit literally issues "
                        + "a complete zero bit block followed by a complete one "
                        + "bit block in each pair. For every number r of pairs the "
                        + "first source survives with value v1 plus the sum over "
                        + "i<r of coefficient(k,phi1+2i+1), phase phi1+2r and a "
                        + "tail below k. If the actual endpoint readings of the two "
                        + "sources agree after every r from zero through T pairs, "
                        + "their initial phases are equal. The sampled offsets "
                        + "cover every residue because two is a unit modulo odd T. "
                        + "Zero endpoints are also available under the single-bit "
                        + "alphabet; the implication already uses only the pair "
                        + "endpoints. T pairs contain 2T actual single-bit actions. "
                        + "This theorem supplies the odd-period phase recovery "
                        + "case. The even-period protocol, the p-1 sample argument "
                        + "for wider blocks, and the overall acquisition bound "
                        + "are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-even-single-bit-phase-recovery"),
                DeclarationHandle.Create(Owner + "even_single_bit_phase_recovery"),
                H("The even-period single-bit protocol recovers the initial phase"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("v1"), Colon, Sp, Call("ZMod",
                    D(2)), Comma, Sp, F.Id("v2"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("phi1"), Colon, Sp, Call("ZMod",
                    Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("phi2"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))),
                    Comma, Sp, F.Id("s1"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("s2"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close),
                    Sp, Land, Sp, Seq(Open, Call("Even", Seq(F.Id("k"), Plus, D(1))), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s1"),
                    Sp, Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s2"), Sp, Lt, Sp, F.Id("k")), Close)), Close),
                    Sp, Implies, Sp, Seq(Open, Seq(Seq(Open, Seq(Forall, Sp, F.Id("r"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
                    Comma, Sp, Seq(Open, Seq(Exists, Sp, F.Id("value"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("s0"),
                    Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(F.Id("s0"), Sp, Lt, Sp, F.Id("k")),
                    Close), Sp, Land, Sp, Seq(Open, Seq(Call("evenSingleBitOrbit", F.Id("k"), F.Id("r"), Call("some", F.Id("v1"),
                    F.Id("phi1"), F.Id("s1"))), Sp, Eq, Sp, Call("some", F.Id("value"), Seq(Seq(F.Id("phi1"), Plus, D(1)), Plus,
                    Seq(F.Id("r"), Sp, Cdot, Sp, D(2))), F.Id("s0"))), Close)), Close)), Close)), Close), Sp, Land, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(Forall, Sp, F.Id("r"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(F.Id("r"), Sp, Leq, Sp, Seq(Seq(Open, Seq(F.Id("k"), Plus, D(1)), Close), Slash, D(2))), Close), Sp, Implies,
                    Sp, Seq(Open, Seq(Call("endpointReading", Call("alternatingBitOrbit", F.Id("k"), F.Id("r"), Call("some", F.Id("v1"),
                    F.Id("phi1"), F.Id("s1")))), Sp, Eq, Sp, Call("endpointReading", Call("alternatingBitOrbit", F.Id("k"), F.Id("r"),
                    Call("some", F.Id("v2"), F.Id("phi2"), F.Id("s2"))))), Close)), Close)), Close), Sp, Implies, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(Forall, Sp, F.Id("r"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(F.Id("r"), Sp, Leq, Sp, Seq(Seq(Open, Seq(F.Id("k"), Plus, D(1)), Close), Slash, D(2))), Close), Sp, Implies,
                    Sp, Seq(Open, Seq(Call("endpointReading", Call("evenSingleBitOrbit", F.Id("k"), F.Id("r"), Call("some", F.Id("v1"),
                    F.Id("phi1"), F.Id("s1")))), Sp, Eq, Sp, Call("endpointReading", Call("evenSingleBitOrbit", F.Id("k"), F.Id("r"),
                    Call("some", F.Id("v2"), F.Id("phi2"), F.Id("s2"))))), Close)), Close)), Close), Sp, Implies, Sp, Seq(Open,
                    Seq(F.Id("phi1"), Sp, Eq, Sp, F.Id("phi2")), Close)), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k>=2 with even T=k+1, arbitrary initial scalar values "
                        + "and ambient phases, and two initial tails below k, the literal "
                        + "single-bit protocol is (01)^(T/2), then a zero, then "
                        + "(01)^(T/2). Its second half survives for every number r "
                        + "of pairs with phase phi1+1+2r and a tail below k. Equality "
                        + "of the two sources' actual endpoints after every r from "
                        + "zero through T/2 in each half implies equality of their "
                        + "INITIAL phases. Differences of adjacent pair endpoints "
                        + "give the odd and even coefficient offsets, including "
                        + "offset zero at the final even sample. The protocol uses "
                        + "2T+1 complete single-bit actions; it reads no hidden "
                        + "clock or unread bit. Target decoder and global cost "
                        + "integration belong to the full acquisition construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-safe-block-phase-recovery"),
                DeclarationHandle.Create(Owner + "safe_block_phase_recovery"),
                H("The safe p-minus-one block archive recovers endpoint subgroup phase"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("v1"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("v2"), Colon, Sp, Call("ZMod",
                    D(2)), Comma, Sp, F.Id("phi1"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("phi2"),
                    Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("s1"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
                    Comma, Sp, F.Id("s2"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open,
                    Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("m")), Close),
                    Sp, Land, Sp, Seq(Open, Seq(F.Id("s1"), Sp, Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s2"),
                    Sp, Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Call("divides", Call("gcd", F.Id("m"), Seq(F.Id("k"),
                    Plus, D(1))), Call("val", F.Id("phi1"))), Close), Sp, Land, Sp, Seq(Open, Call("divides", Call("gcd", F.Id("m"),
                    Seq(F.Id("k"), Plus, D(1))), Call("val", F.Id("phi2"))), Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(Seq(Open,
                    Call("DBonacciAdmissible", F.Id("k"), F.Id("m"), Call("isolatedProbe", F.Id("m"), Call("phaseProbeOffset",
                    F.Id("k"), F.Id("m")))), Close), Sp, Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("r"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Exists, Sp, F.Id("value"), Colon, Sp, Call("ZMod", D(2)), Comma,
                    Sp, F.Id("phi"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("s0"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(F.Id("s0"), Sp, Lt, Sp, F.Id("k")), Close), Sp, Land,
                    Sp, Seq(Open, Seq(Call("iterate", Call("runBits", F.Id("k"), Call("isolatedProbe", F.Id("m"), Call("phaseProbeOffset",
                    F.Id("k"), F.Id("m")))), F.Id("r"), Call("some", F.Id("v1"), F.Id("phi1"), F.Id("s1"))), Sp, Eq, Sp, Call("some",
                    F.Id("value"), F.Id("phi"), F.Id("s0"))), Close)), Close)), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(Forall, Sp, F.Id("r"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(F.Id("r"),
                    Sp, Leq, Sp, Seq(Seq(Seq(Open, Seq(F.Id("k"), Plus, D(1)), Close), Slash, Call("gcd", F.Id("m"), Seq(F.Id("k"),
                    Plus, D(1)))), Minus, D(1))), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("endpointReading", Call("iterate",
                    Call("runBits", F.Id("k"), Call("isolatedProbe", F.Id("m"), Call("phaseProbeOffset", F.Id("k"), F.Id("m")))),
                    F.Id("r"), Call("some", F.Id("v1"), F.Id("phi1"), F.Id("s1")))), Sp, Eq, Sp, Call("endpointReading", Call("iterate",
                    Call("runBits", F.Id("k"), Call("isolatedProbe", F.Id("m"), Call("phaseProbeOffset", F.Id("k"), F.Id("m")))),
                    F.Id("r"), Call("some", F.Id("v2"), F.Id("phi2"), F.Id("s2"))))), Close)), Close)), Close), Sp, Implies, Sp,
                    Seq(Open, Seq(F.Id("phi1"), Sp, Eq, Sp, F.Id("phi2")), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k>=2 and m>=2, set g=gcd(m,k+1), p=(k+1)/g "
                        + "and j=1 if g=1, otherwise j=g-1. For arbitrary values, "
                        + "ambient phases whose natural representatives are divisible "
                        + "by g, and old tails below k, isolatedProbe(m,j) is locally "
                        + "legal and every repeated execution remains live. Equal "
                        + "endpoint readings after every r from zero through p-1 "
                        + "imply equality of the INITIAL phases. When p=1 each "
                        + "phase is zero, so no block is needed. Otherwise the "
                        + "proof recovers the one omitted sample using invariance "
                        + "of a complete cycle sum under rotation of the same "
                        + "endpoint subgroup. For g>=2 the sampled coset has one "
                        + "coefficient support position; for g=1 full translated "
                        + "coefficient equality forces the phase shift to vanish. "
                        + "No mod-two nonzero interpretation of the integer total "
                        + "two is used, and no unknown initial length is read."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Comma);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
