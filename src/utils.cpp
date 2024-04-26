#include "utils.h"
#include <chrono>

static array<decltype(std::chrono::high_resolution_clock::now()), max_stopwatch_idx + 1> start_time;
static array<decltype(std::chrono::high_resolution_clock::now()), max_stopwatch_idx + 1> end_time;
static array<uint64_t, max_stopwatch_idx + 1> total_time;

void start_watch(stopwatch_idx idx) {
    assert(idx >= 0 && idx <= max_stopwatch_idx);
    start_time[(unsigned)idx] = std::chrono::high_resolution_clock::now();
}

uint64_t stop_watch(stopwatch_idx idx) {
    end_time[(unsigned)idx] = std::chrono::high_resolution_clock::now();
    uint64_t res = std::chrono::duration_cast<std::chrono::microseconds>(end_time[idx] - start_time[idx]).count();
    total_time[(unsigned)idx] += res;
    return res / 1000;
}

uint64_t peek_watch(stopwatch_idx idx) {
    auto now = std::chrono::high_resolution_clock::now();
    return std::chrono::duration_cast<std::chrono::microseconds>(now - start_time[idx]).count() / 1000;
}

uint64_t get_total_time(stopwatch_idx idx) {
    return total_time[(unsigned)idx] / 1000;
}
