#ifndef _SATTERMINATION_INCLUDED
#define _SATTERMINATION_INCLUDED

bool* ensure_termination_after(void* solver, long long limit_in_miliseconds);
void stop_termination_checking(bool* stopFlag);


#endif
