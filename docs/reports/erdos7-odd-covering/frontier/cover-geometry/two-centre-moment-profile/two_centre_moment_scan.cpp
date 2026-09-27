// Exact two-profile engine for the moment continuation profile constructor.
// Enumerates the 16^5 two-center root/equality layouts and both ternary
// endpoint masses once. The input contains mass and second-moment gate rows.
// All arithmetic affecting an extremum is signed 128-bit integer arithmetic;
// the input and accumulation bounds are checked before the scan.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Int = __int128_t;
const Int LIMIT = (Int(1) << 126) - 1;
const int OUTSIDE_DENOMINATOR = 6 * 10 * 12 * 16 * 18;
const int SCREEN_DENOMINATOR = 12 * OUTSIDE_DENOMINATOR;
const int LAYOUTS = 1 << 20;

Int read_nonnegative(std::istream &input) {
    std::string text;
    if (!(input >> text) || text.empty()) throw std::runtime_error("missing integer");
    Int value = 0;
    for (char digit : text) {
        if (digit < '0' || digit > '9') throw std::runtime_error("invalid integer");
        if (value > (LIMIT - (digit - '0')) / 10)
            throw std::runtime_error("input exceeds integer bound");
        value = 10 * value + digit - '0';
    }
    return value;
}

std::string decimal(Int value) {
    if (value == 0) return "0";
    bool negative = value < 0;
    if (negative) value = -value;
    std::string result;
    while (value) {
        result.push_back(char('0' + value % 10));
        value /= 10;
    }
    if (negative) result.push_back('-');
    std::reverse(result.begin(), result.end());
    return result;
}

struct Extremum {
    Int minimum = LIMIT;
    Int maximum = -LIMIT;
    int minimum_code = -1;
    int maximum_code = -1;
    std::uint64_t minimum_ties = 0;
    std::uint64_t maximum_ties = 0;
    std::uint64_t cases = 0;
    void include(Int value, int code) {
        ++cases;
        if (value < minimum) { minimum = value; minimum_code = code; minimum_ties = 1; }
        else if (value == minimum) ++minimum_ties;
        if (value > maximum) { maximum = value; maximum_code = code; maximum_ties = 1; }
        else if (value == maximum) ++maximum_ties;
    }
};

struct Profile {
    int identifier;
    Int gain;
    std::array<Int, 192> coefficient;
    std::array<Extremum, 2> endpoint;
};

int main(int argc, char **argv) {
    try {
        if (argc != 2) throw std::runtime_error("usage: engine coefficient-file");
        std::ifstream input(argv[1]);
        if (!input) throw std::runtime_error("cannot open coefficient file");
        const Int denominator = read_nonnegative(input);
        if (denominator == 0 || denominator > LIMIT / SCREEN_DENOMINATOR)
            throw std::runtime_error("invalid common denominator");
        std::array<Profile, 2> profiles;
        for (int index = 0; index < 2; ++index) {
            if (read_nonnegative(input) != index)
                throw std::runtime_error("invalid profile identifier");
            profiles[index].identifier = index;
            profiles[index].gain = read_nonnegative(input);
            Int bound = profiles[index].gain;
            for (Int &coefficient : profiles[index].coefficient) {
                coefficient = read_nonnegative(input);
                if (bound > LIMIT - coefficient)
                    throw std::runtime_error("coefficient sum overflow");
                bound += coefficient;
            }
            if (bound > LIMIT / SCREEN_DENOMINATOR)
                throw std::runtime_error("accumulation exceeds signed integer bound");
        }
        std::string extra;
        if (input >> extra) throw std::runtime_error("unexpected coefficient input");

        const int caps[5] = {6, 10, 12, 16, 18};
        int grid[32][8];
        int screens[192];
        for (int code = 0; code < LAYOUTS; ++code) {
            int remaining = code;
            int row[5], column[5], equal_roots[5];
            for (int index = 0; index < 5; ++index) {
                int role = remaining & 15;
                remaining >>= 4;
                row[index] = role & 1;
                column[index] = (role >> 1) & 3;
                equal_roots[index] = (role >> 3) & 1;
            }
            for (int cell = 0; cell < 8; ++cell) {
                if (cell == 0) {
                    for (int support = 0; support < 32; ++support) grid[support][cell] = 0;
                    continue;
                }
                int factors[5];
                int value = 1;
                for (int index = 0; index < 5; ++index) {
                    int a = (cell / 4 == row[index]);
                    int b = (cell % 4 == column[index]);
                    factors[index] = caps[index] - a - b + equal_roots[index] * a * b;
                    value *= factors[index];
                }
                grid[0][cell] = value;
                // A support coordinate removes its star factor: replace
                // caps[index]-number_of_forbidden_roots by caps[index].
                for (int support = 1; support < 32; ++support) {
                    int index = __builtin_ctz(unsigned(support));
                    int numerator = grid[support ^ (1 << index)][cell] * caps[index];
                    if (numerator % factors[index] != 0)
                        throw std::runtime_error("nonintegral support expansion");
                    grid[support][cell] = numerator / factors[index];
                }
            }
            for (int t = 1; t <= 2; ++t) {
                for (int support = 0; support < 32; ++support) {
                    int sum0 = 0, sum1 = 0, maximum0 = 0, maximum1 = 0, column_maximum = 0;
                    for (int column_index = 0; column_index < 4; ++column_index) {
                        int a = grid[support][column_index];
                        int b = grid[support][column_index + 4];
                        sum0 += a; sum1 += b;
                        maximum0 = std::max(maximum0, a);
                        maximum1 = std::max(maximum1, b);
                        column_maximum = std::max(column_maximum, t * a + (3 - t) * b);
                    }
                    screens[support] = t * sum0 + (3 - t) * sum1;
                    screens[32 + support] = 4 * column_maximum;
                    screens[64 + support] = std::max(t * sum0, (3 - t) * sum1);
                    screens[96 + support] = std::max(sum0, sum1);
                    screens[128 + support] = 4 * std::max(t * maximum0, (3 - t) * maximum1);
                    screens[160 + support] = 4 * std::max(maximum0, maximum1);
                }
                for (Profile &profile : profiles) {
                    Int gate = profile.gain * screens[0];
                    for (int index = 0; index < 192; ++index)
                        gate -= profile.coefficient[index] * screens[index];
                    profile.endpoint[t - 1].include(gate, code);
                }
            }
        }
        std::cout << decimal(denominator * SCREEN_DENOMINATOR) << '\n';
        for (const Profile &profile : profiles) {
            for (int t = 1; t <= 2; ++t) {
                const Extremum &result = profile.endpoint[t - 1];
                std::cout << profile.identifier << ' ' << t << ' '
                          << decimal(result.minimum) << ' ' << decimal(result.maximum) << ' '
                          << result.minimum_code << ' ' << result.maximum_code << ' '
                          << result.minimum_ties << ' ' << result.maximum_ties << ' '
                          << result.cases << '\n';
            }
        }
        return 0;
    } catch (const std::exception &error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
