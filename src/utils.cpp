#include "utils.h"
#include <chrono>

static decltype(std::chrono::high_resolution_clock::now()) start_time;
static decltype(std::chrono::high_resolution_clock::now()) end_time;

void start_watch() {
    start_time = std::chrono::high_resolution_clock::now();
}

uint64_t stop_watch() {
    end_time = std::chrono::high_resolution_clock::now();
    return std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
}
